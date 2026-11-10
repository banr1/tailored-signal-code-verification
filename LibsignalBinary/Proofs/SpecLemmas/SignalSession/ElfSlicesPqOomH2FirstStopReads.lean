/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib.FsTrace
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsMusl
meta import ProofLib
meta import ProofLib.ProgramReflection

/-!
# Real-Run First-Stop Lemmas for `readFile` (`0x4691b4`) & `readStdin` (`0x469000`) (`ElfSlicesPqOomH2FirstStopReads`)

**Checked by Lean.**

Discharges the real-run first-stop (`(R)`) obligations for the two CLI read ghost hooks in
`hole2_ghFixed` (`f3ReadFileFixedGhostHookFine` at `0x4691b4#64` and `f3ReadStdinGhostHookFine`
at `0x469000#64`) without touching any hook definitions or `ElfSlicesPqOomPlacedInst`:

1. **`readFile` (`0x4691b4#64`, `h2fsreads_readFile_firstStop` / `h2fsreads_readFile_emptyProg_firstStop`):**
   From `mallocngLib.LinkedAt cliElfBytes mmpl`, `ActiveF3CallPre` for `readFileAnySpecPlaced` at
   `ReadFileRuleEnvFixed cliIo.rd`, `h2fsreads_keep (s0.readReg64 .lr) = false` (`[0x4686a0, 0x468724) ∪ [0x469000, 0x46f000)`),
   `ExecFrozen s0.mem`, `f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep s0.mem)`, and
   `FdsGe3Closed s0.fs` (`F3ReadFileFixedCallGuard s0`, which supplies `s0.fs.allocFd ≠ none` via
   `allocFd_ne_none_of_fdsGe3Closed`), proves `subroutine_ok f3TrialRxProg 0x4691b4#64
   (readFileAnyBudgetCondSpec ...)` from `mallocng` + `musl` + `signalSessionIoMultiLib` and lifts
   `subroutine_ok_readFileAnyNoOom_of_cond` via `real_f3ReadFileFixed_run_of_stripS` to a real
   first-stop run `StepsUntil P (SubroutineStop s0) (s0.setPC 0x4691b4#64) sf` with
   `sf.fs = s0.fs`, `sf.trace = s0.trace`, `FsTraced IsFsC s0 sf`, `FdsGe3Closed sf.fs`, and
   `ExecFrozen sf.mem` — plus `ActiveF3ReadFileRun` and exact agreement with
   `f3ReadFileFixedGhostHookFine` (killing its `f3ReadFileFallback` branch).
2. **`readStdin` (`0x469000#64`, `h2fsreads_readStdin_firstStop` / `h2fsreads_readStdin_emptyProg_firstStop`):**
   From `mallocngLib.LinkedAt cliElfBytes mmpl`, `ActiveF3CallPre` for `readStdinSpecOfPlaced` at
   `ReadStdinBoundedEnv`, `h2fsreads_keep (s0.readReg64 .lr) = false`, `ExecFrozen s0.mem`, and
   `f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep s0.mem)` (**`0` `FdsGe3Closed`
   premise**), proves `subroutine_ok f3TrialRxProg 0x469000#64 (readStdinBudgetCondSpec ...)` and
   lifts `subroutine_ok_readStdinNoOom_of_cond` via `real_readStdin_run_of_stripS` to a real
   first-stop run `StepsUntil P (SubroutineStop s0) (s0.setPC 0x469000#64) sf` with
   `sf.fs.files = s0.fs.files`, `sf.trace = s0.trace`, `FsTraced IsFsC s0 sf`,
   `(FdsGe3Closed s0.fs → FdsGe3Closed sf.fs)`, and `ExecFrozen sf.mem` (note `read(0, ...)`
   advances fd `0`'s read offset on non-empty `stdin`, so `sf.fs.files = s0.fs.files` and
   `FsTraced IsFsC s0 sf` hold rather than `sf.fs = s0.fs`) — plus `ActiveReadStdinLinkedRun` and
   exact agreement with `f3ReadStdinGhostHookFine` (killing its `f3ReadStdinFallback` branch).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads

open Arm64 (FsTraced GhostName Program State Steps StepsUntil SubroutineStop subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (ActiveF3ReadFileRun F3ReadFileFixedCallGuard f3ReadFileFixedGhostHookFine
   f3ReadFileFixedGhostHookFineSub readFileAnyBudgetCondSpec readFileAnySpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (ActiveReadStdinLinkedRun readStdinBudgetCondSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3ReadStdinGhostHookFine f3ReadStdinGhostHookFineSub)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (ReadStdinBoundedEnv readStdinSpecOfPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
  (h2fsalloc_StepsUntilInKeep h2fsalloc_stepsUntilInKeep_of_allProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper
  (h2fsreads_fineHookAllocEntries_thunks h2fsreads_keepSub_mallocng h2fsreads_muslOpenRdonlyDet_ok
   h2fsreads_noAllocShim_ok h2fsreads_stdMemcpy_ok h2fsreads_toNat_add_ofNat_of_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsMusl
  (h2fsreads_muslClose48Local_ok h2fsreads_muslErrnoLocation_ok h2fsreads_muslReadDir32_ok
   h2fsreads_muslReadFileOrStdio32_ok h2fsreads_muslReadStdin32_ok)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_ghFixed hole2_hookStack hole2_keep hole2_keepSub)
open ProofLib (stripExecOutside)

abbrev h2fsreads_hookStack : Nat :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper.h2fsreads_hookStack

abbrev h2fsreads_keepSub : BitVec 64 → Bool :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper.h2fsreads_keepSub

abbrev h2fsreads_keep : BitVec 64 → Bool :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper.h2fsreads_keep

abbrev h2fsreads_emptyProg : Program :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReadsHelper.h2fsreads_emptyProg

section H2FsReadsPriv

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open ProofLib.SepLogic SepProp
open CryptoVerification (signalSessionIoMultiLib)
open LibsignalBinary.Heap.Fine (f3RxWordCount fineCostModel)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook (
  ActiveF3ReadFilePre f3ReadFileFixedGhostHook f3ReadFileLinkedHook
  fineHookRustCliAllocBudget_pool_stripS real_f3ReadFileFixed_run_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst (
  cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded fineHookPoolErrnoSplit
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (
  CompiledReadStdinEnv compiledReadStdinEnv_sub_bounded fitsEnv_compiled_of_sub
  real_readStdin_run_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst (
  cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3ReadStdinPre f3ReadStdinGhostHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (
  codeLoaded_of_checkProgSliceInWordTree
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (ExternPreservesOracleSymtab)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoReadsCodeLoaded cliIoReadFileSym cliIoReadStdinSym cliIoReadsCodeLoaded_of_blocks
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_svc
  f3TrialRxWordTree_eq f3TrialRxWordTree_size f3Trial_allocMemcpyVm_ok
)

/-! ## `signalSessionIoMultiLib` Placement and First-Stop Theorems -/

private def h2fsreads_ioMpl : MultiPlacement where
  base i := [0x469000#64, 0x468724#64, 0x468854#64, 0x4691b4#64, 0x4693f0#64].getD i 0#64
  ρ s :=
    if s == "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" then 0x469630#64
    else if s == "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" then 0x469634#64
    else if s == "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" then 0x469638#64
    else if s == "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" then 0x469640#64
    else if s == "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" then 0x468964#64
    else if s == "__errno_location" then 0x46ba94#64
    else if s == "close" then 0x46e1fc#64
    else if s == "memcpy" then 0x469650#64
    else if s == "open" then 0x46bb24#64
    else if s == "read" then 0x46e240#64
    else if s == "write" then 0x46e274#64
    else 0#64

private theorem h2fsreads_ioMpl_placeable :
    signalSessionIoMultiLib.Placeable h2fsreads_ioMpl :=
  signalSessionIoMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

private theorem h2fsreads_readsCodeLoaded (m : Memory)
    (hCL : f3TrialRxProg.CodeLoaded m) :
    CliIoReadsCodeLoaded h2fsreads_ioMpl m :=
  cliIoReadsCodeLoaded_of_blocks
    (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)
    (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)
    (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)

private theorem h2fsreads_keepSub_imp_keep (a : BitVec 64)
    (h : h2fsreads_keepSub a = true) : h2fsreads_keep a = true :=
  decide_eq_true (Or.inr (of_decide_eq_true h))

private theorem h2fsreads_keep_false_imp_keepSub_false (a : BitVec 64)
    (h : h2fsreads_keep a = false) : h2fsreads_keepSub a = false := by
  cases hs : h2fsreads_keepSub a
  · rfl
  · rw [h2fsreads_keepSub_imp_keep a hs] at h
    cases h

private theorem h2fsreads_rx_codeLoaded_stripSub_of_keep {m : Memory}
    (hL : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep m)) :
    f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keepSub m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hbase_eq : f3TrialRxProg.base = 0x469000#64 := by
    rw [f3TrialRxProg_base]; decide
  have hlen_eq : f3TrialRxProg.code.length = 0x6000 := by
    have hl : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
      rw [f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size]
    rw [hl]; decide
  have hi' : i < 0x6000 := hlen_eq ▸ hi
  have ha_nat : (f3TrialRxProg.base + BitVec.ofNat 64 i).toNat = 0x469000 + i := by
    rw [hbase_eq]
    exact h2fsreads_toNat_add_ofNat_of_lt (by show 0x469000 + i < 18446744073709551616; omega)
  have hsub : h2fsreads_keepSub (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
    unfold h2fsreads_keepSub
    exact decide_eq_true ⟨by omega, by omega⟩
  have hkeep : h2fsreads_keep (f3TrialRxProg.base + BitVec.ofNat 64 i) = true :=
    h2fsreads_keepSub_imp_keep _ hsub
  have hb := hL.byte_eq i hi
  have hp := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [strip_read8] at hb ⊢
  rw [strip_perm_of_keep hkeep] at hp
  rw [strip_perm_of_keep hsub]
  rw [strip_isLazyFree] at hlf ⊢
  exact ⟨hb, hp, hlf⟩

private theorem h2fsreads_emptyProg_no_ext (pc : BitVec 64) :
    h2fsreads_emptyProg.externAt? pc = none := rfl

private theorem h2fsreads_pre_compiled_of_bounded [LibsignalPlacement]
    {γ : GhostName} {mmpl : MultiPlacement} {tp : BitVec 64}
    {y : CryptoVerification.SignalSession.Cli.MainHops.ReadStdinGhost × fineCostModel.σ}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack ReadStdinBoundedEnv).pre y s0 ∗ R) :
    s0.mem ⊨
      (readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack CompiledReadStdinEnv).pre y s0 ∗ R := by
  rcases y with ⟨x, st⟩
  dsimp only [readStdinSpecOfPlaced] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hpre.1.1, hpre.1.2.1,
    fitsEnv_compiled_of_sub (fun _ => compiledReadStdinEnv_sub_bounded) hpre.1.2.2.1,
    hpre.1.2.2.2⟩, hpre.2⟩

end H2FsReadsPriv

/-- Budget-conditional `subroutine_ok` for `signal_session_io::read_file` at `0x4691b4#64` on
    `f3TrialRxProg`, proved from `mallocng` + `musl` + `signalSessionIoMultiLib`. -/
theorem h2fsreads_readFileCond_ok
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg 0x4691b4#64
      (readFileAnyBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  have hres : Arm64.Obj.MultiPlacedLib.resolve
      CryptoVerification.signalSessionIoMultiLib h2fsreads_ioMpl
      LibsignalBinary.Proofs.SignalSession.CliIo.Sym.cliIoReadFileSym = 0x4691b4#64 := rfl
  rw [← hres]
  exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst.cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded
    (LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst.fineHookPoolErrnoSplit
      γ mmpl tp cliElfImage.brkStart)
    cliBudgetLimits h2fsreads_ioMpl_placeable h2fsreads_readsCodeLoaded (by decide)
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
    (LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon.ExternPreservesOracleSymtab.of_no_extern
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext)
    (fun _ _ => LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext _)
    (fun _ _ => LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext _)
    h2fsreads_muslOpenRdonlyDet_ok h2fsreads_muslErrnoLocation_ok h2fsreads_muslReadDir32_ok
    h2fsreads_muslReadFileOrStdio32_ok h2fsreads_muslClose48Local_ok h2fsreads_stdMemcpy_ok
    h2fsreads_noAllocShim_ok (h2fsreads_fineHookAllocEntries_thunks mmpl hMm γ tp)

/-- Budget-conditional `subroutine_ok` for `signal_session_io::read_stdin` at `0x469000#64` on
    `f3TrialRxProg`, proved from `mallocng` + `musl` + `signalSessionIoMultiLib`. -/
theorem h2fsreads_readStdinCond_ok
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg 0x469000#64
      (readStdinBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  have hres : Arm64.Obj.MultiPlacedLib.resolve
      CryptoVerification.signalSessionIoMultiLib h2fsreads_ioMpl
      LibsignalBinary.Proofs.SignalSession.CliIo.Sym.cliIoReadStdinSym = 0x469000#64 := rfl
  rw [← hres]
  have hEntries := h2fsreads_fineHookAllocEntries_thunks mmpl hMm γ tp
  exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst.cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    h2fsreads_ioMpl_placeable (Nat.le_refl _) h2fsreads_readsCodeLoaded
    (fun _ _ => LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext _)
    (fun _ _ => LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext _)
    h2fsreads_muslReadStdin32_ok
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_allocMemcpyVm_ok
    h2fsreads_noAllocShim_ok
    (hEntries.alloc cliBudgetLimits) (hEntries.realloc cliBudgetLimits)
    (hEntries.dealloc cliBudgetLimits)
    (fun hsat hmap =>
      LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.fineHookRustCliAllocBudget_mapped_lt_userVa
        (by decide) hsat hmap)

/-- Real first-stop run of `signal_session_io::read_file` (`0x4691b4#64`) on any
`Syscall.standard` program `P` extern-free on `h2fsreads_keepSub` (`[0x469000, 0x46f000)`), under
`FdsGe3Closed s0.fs` (`F3ReadFileFixedCallGuard s0`, supplying `s0.fs.allocFd ≠ none` for `open()`). -/
theorem h2fsreads_readFile_firstStop
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hno : ∀ pc, h2fsreads_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hlr : h2fsreads_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC 0x4691b4#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      FdsGe3Closed sf.fs ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSat⟩ := hPre
  have hlrSub : h2fsreads_keepSub (s0.readReg64 .lr) = false :=
    h2fsreads_keep_false_imp_keepSub_false _ hlr
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keepSub s0.mem) :=
    h2fsreads_rx_codeLoaded_stripSub_of_keep hCode
  have hKeepMng := h2fsreads_keepSub_mallocng mmpl hMm
  obtain ⟨sf, huntil, hstop, _, hfs_eq, htr_eq, hfr_sf⟩ :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.real_f3ReadFileFixed_run_of_stripS
      hsvc LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      hno LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (fun st' s' =>
        LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.fineHookRustCliAllocBudget_pool_stripS
          γ mmpl tp cliElfImage.brkStart hKeepMng cliBudgetLimits st' s')
      (h2fsreads_readFileCond_ok mmpl hMm γ tp)
      hRun hSp hSat hFr hlrSub hFs hCodeSub
  exact ⟨sf, huntil, hstop, hfs_eq, htr_eq,
    FsTraced.of_eq htr_eq (congrArg Arm64.FsState.files hfs_eq), hfs_eq ▸ hFs, hfr_sf⟩

/-- Instantiates `h2fsreads_readFile_firstStop` at `h2fsreads_emptyProg`, discharging
`ActiveF3ReadFileRun` and equating `sf` with `f3ReadFileFixedGhostHookFine ... s0`. -/
theorem h2fsreads_readFile_emptyProg_firstStop
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hlr : h2fsreads_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    ActiveF3ReadFileRun h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
        0x4691b4#64 F3ReadFileFixedCallGuard s0 ∧
      ∃ sf : State,
        sf = f3ReadFileFixedGhostHookFine h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
          0x4691b4#64 mmpl cliElfImage.brkStart cliBudgetLimits h2fsreads_hookStack s0 ∧
        StepsUntil h2fsreads_emptyProg (SubroutineStop s0) (s0.setPC 0x4691b4#64) sf ∧
        SubroutineStop s0 sf ∧
        sf.fs = s0.fs ∧
        sf.trace = s0.trace ∧
        FsTraced IsFsC s0 sf ∧
        FdsGe3Closed sf.fs ∧
        ExecFrozen sf.mem := by
  classical
  have hlrSub : h2fsreads_keepSub (s0.readReg64 .lr) = false :=
    h2fsreads_keep_false_imp_keepSub_false _ hlr
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keepSub s0.mem) :=
    h2fsreads_rx_codeLoaded_stripSub_of_keep hCode
  obtain ⟨sf, huntil, hstop, hfs_eq, htr_eq, hfsT, hFs_sf, hfr_sf⟩ :=
    h2fsreads_readFile_firstStop hMm rfl (fun pc _ => h2fsreads_emptyProg_no_ext pc)
      hPre hlr hFr hCode hFs
  have hReal : ActiveF3ReadFileRun h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
      0x4691b4#64 F3ReadFileFixedCallGuard s0 :=
    ⟨hFr, hlrSub, hFs, hCodeSub, sf, huntil, hstop, hfs_eq, htr_eq, hfr_sf⟩
  have hActPre :
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.ActiveF3ReadFilePre
        (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack (ReadFileRuleEnvFixed cliIo.rd) s0 := hPre
  have hhook_eq :
      f3ReadFileFixedGhostHookFine h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
        0x4691b4#64 mmpl cliElfImage.brkStart cliBudgetLimits h2fsreads_hookStack s0 =
        Classical.choose hReal.2.2.2.2 := by
    unfold f3ReadFileFixedGhostHookFine
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileLinkedHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2.2
  have hdet : sf = Classical.choose hReal.2.2.2.2 :=
    StepsUntil.deterministic huntil hstop hchoose.1 hchoose.2.1
  exact ⟨hReal, sf, hdet.trans hhook_eq.symm, huntil, hstop, hfs_eq, htr_eq, hfsT, hFs_sf, hfr_sf⟩

/-- Real first-stop run of `signal_session_io::read_stdin` (`0x469000#64`) on any
`Syscall.standard` program `P` extern-free on `h2fsreads_keepSub` (`[0x469000, 0x46f000)`; note
`read(0, ...)` advances fd `0`'s offset on non-empty `stdin`, so `sf.fs.files = s0.fs.files` and
`FdsGe3Closed s0.fs → FdsGe3Closed sf.fs` hold with `0` `FdsGe3Closed` premise). -/
theorem h2fsreads_readStdin_firstStop [LibsignalPlacement]
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hno : ∀ pc, h2fsreads_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack ReadStdinBoundedEnv) s0)
    (hlr : h2fsreads_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC 0x469000#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSatB⟩ := hPre
  have hSatC := h2fsreads_pre_compiled_of_bounded hSatB
  have hlrSub : h2fsreads_keepSub (s0.readReg64 .lr) = false :=
    h2fsreads_keep_false_imp_keepSub_false _ hlr
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keepSub s0.mem) :=
    h2fsreads_rx_codeLoaded_stripSub_of_keep hCode
  have hKeepMng := h2fsreads_keepSub_mallocng mmpl hMm
  obtain ⟨sf, huntil, hstop, _, hfiles, htr_eq, hfds, hfr_sf⟩ :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.real_readStdin_run_of_stripS
      hsvc LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      hno LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (fun st' s' =>
        LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.fineHookRustCliAllocBudget_pool_stripS
          γ mmpl tp cliElfImage.brkStart hKeepMng cliBudgetLimits st' s')
      (h2fsreads_readStdinCond_ok mmpl hMm γ tp)
      hRun hSp hSatC hFr hlrSub hCodeSub
  exact ⟨sf, huntil, hstop, hfiles, htr_eq, FsTraced.of_eq htr_eq hfiles, hfds, hfr_sf⟩

/-- Instantiates `h2fsreads_readStdin_firstStop` at `h2fsreads_emptyProg`, discharging
`ActiveReadStdinLinkedRun` and equating `sf` with `f3ReadStdinGhostHookFine ... s0`. -/
theorem h2fsreads_readStdin_emptyProg_firstStop [LibsignalPlacement]
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack ReadStdinBoundedEnv) s0)
    (hlr : h2fsreads_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keep s0.mem)) :
    ActiveReadStdinLinkedRun h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg 0x469000#64 s0 ∧
      ∃ sf : State,
        sf = f3ReadStdinGhostHookFine h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
          0x469000#64 mmpl cliElfImage.brkStart cliBudgetLimits h2fsreads_hookStack s0 ∧
        StepsUntil h2fsreads_emptyProg (SubroutineStop s0) (s0.setPC 0x469000#64) sf ∧
        SubroutineStop s0 sf ∧
        sf.fs.files = s0.fs.files ∧
        sf.trace = s0.trace ∧
        FsTraced IsFsC s0 sf ∧
        (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
        ExecFrozen sf.mem := by
  classical
  have hlrSub : h2fsreads_keepSub (s0.readReg64 .lr) = false :=
    h2fsreads_keep_false_imp_keepSub_false _ hlr
  have hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside h2fsreads_keepSub s0.mem) :=
    h2fsreads_rx_codeLoaded_stripSub_of_keep hCode
  obtain ⟨sf, huntil, hstop, hfiles, htr_eq, hfsT, hfds, hfr_sf⟩ :=
    h2fsreads_readStdin_firstStop hMm rfl (fun pc _ => h2fsreads_emptyProg_no_ext pc)
      hPre hlr hFr hCode
  have hReal : ActiveReadStdinLinkedRun h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
      0x469000#64 s0 :=
    ⟨hFr, hlrSub, hCodeSub, sf, huntil, hstop, hfiles, htr_eq, hfds, hfr_sf⟩
  have hActPre :
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.ActiveF3ReadStdinPre
        (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits h2fsreads_hookStack s0 := hPre
  have hhook_eq :
      f3ReadStdinGhostHookFine h2fsreads_keepSub h2fsreads_emptyProg f3TrialRxProg
        0x469000#64 mmpl cliElfImage.brkStart cliBudgetLimits h2fsreads_hookStack s0 =
        Classical.choose hReal.2.2.2 := by
    unfold f3ReadStdinGhostHookFine
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : sf = Classical.choose hReal.2.2.2 :=
    StepsUntil.deterministic huntil hstop hchoose.1 hchoose.2.1
  exact ⟨hReal, sf, hdet.trans hhook_eq.symm, huntil, hstop, hfiles, htr_eq, hfsT, hfds, hfr_sf⟩

/-- Curried budget-conditional `subroutine_ok` for `signal_session_io::read_file` on
`f3TrialRxProg`. -/
theorem h2fsreads_readFileFineSub_cond_ok
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok f3TrialRxProg 0x4691b4#64
        (readFileAnyBudgetCondSpec
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits extHookStack) :=
  h2fsreads_readFileCond_ok mmpl hMm

/-! ## `hole2_keepSub`-Native First-Stop, Visited-PC, and Scoped Lift Lemmas -/

/-- Real first-stop run of `signal_session_io::read_file` (`0x4691b4#64`) directly from
`hole2_keepSub` premises and `FdsGe3Closed s0.fs`. -/
theorem h2fsreads_readFile_firstStop_keepSub
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hno : ∀ pc, hole2_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC 0x4691b4#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      FdsGe3Closed sf.fs ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSat⟩ := hPre
  have hKeepMng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true :=
    h2fsreads_keepSub_mallocng mmpl hMm
  obtain ⟨sf, huntil, hstop, _, hfs_eq, htr_eq, hfr_sf⟩ :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.real_f3ReadFileFixed_run_of_stripS
      hsvc LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      hno LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (fun st' s' =>
        LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.fineHookRustCliAllocBudget_pool_stripS
          γ mmpl tp cliElfImage.brkStart hKeepMng cliBudgetLimits st' s')
      (h2fsreads_readFileCond_ok mmpl hMm γ tp)
      hRun hSp hSat hFr hlrSub hFs hCodeSub
  exact ⟨sf, huntil, hstop, hfs_eq, htr_eq,
    FsTraced.of_eq htr_eq (congrArg Arm64.FsState.files hfs_eq), hfs_eq ▸ hFs, hfr_sf⟩

/-- `ActiveF3ReadFileRun` on `(hole2_keepSub, hole2_emptyProg)` under `hole2_keepSub` premises
and `FdsGe3Closed s0.fs`. -/
theorem h2fsreads_readFile_activeRealRun_keepSub
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    ActiveF3ReadFileRun hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x4691b4#64 F3ReadFileFixedCallGuard s0 := by
  obtain ⟨sf, huntil, hstop, hfs_eq, htr_eq, _, _, hfr_sf⟩ :=
    h2fsreads_readFile_firstStop_keepSub (P := hole2_emptyProg) hMm rfl (fun _ _ => rfl)
      hPre hlrSub hFr hCodeSub hFs
  exact ⟨hFr, hlrSub, hFs, hCodeSub, sf, huntil, hstop, hfs_eq, htr_eq, hfr_sf⟩

/-- `h2fsalloc_StepsUntilInKeep` witness in `hole2_keepSub` for `(hole2_ghFixed mpl mmpl).readFile`. -/
theorem h2fsreads_readFile_stepsUntilInKeep_keepSub [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    let hSub := f3ReadFileFixedGhostHookFineSub hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x4691b4#64 mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    let sf := hSub.val s0
    (hole2_ghFixed mpl mmpl).readFile = some hSub ∧
      h2fsalloc_StepsUntilInKeep hole2_emptyProg hole2_keepSub (SubroutineStop s0)
        (s0.setPC 0x4691b4#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      FdsGe3Closed sf.fs ∧
      ExecFrozen sf.mem := by
  classical
  have hReal : ActiveF3ReadFileRun hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x4691b4#64 F3ReadFileFixedCallGuard s0 :=
    h2fsreads_readFile_activeRealRun_keepSub mmpl hMm hPre hFr hlrSub hCodeSub hFs
  have hActPre :
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.ActiveF3ReadFilePre
        (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd) s0 := hPre
  have heq : (f3ReadFileFixedGhostHookFineSub hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x4691b4#64 mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack).val s0 =
      Classical.choose hReal.2.2.2.2 := by
    change LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHook
      hole2_keepSub hole2_emptyProg f3TrialRxProg 0x4691b4#64
      (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      cliBudgetLimits hole2_hookStack _ s0 = _
    unfold LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHook
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileLinkedHook
    simp only [hActPre, hReal, ↓reduceDIte]
  obtain ⟨hU0, hStop, hFsEq, hTrEq, hFrSf⟩ := Classical.choose_spec hReal.2.2.2.2
  dsimp only
  rw [heq]
  refine ⟨rfl, ?_, hStop, hFsEq, hTrEq,
    FsTraced.of_eq hTrEq (congrArg Arm64.FsState.files hFsEq), hFsEq.symm ▸ hFs, hFrSf⟩
  refine h2fsalloc_stepsUntilInKeep_of_allProg (fun P hsvc hno => ?_) hU0
  obtain ⟨sfP, hUP, hStopP, _, _, _, _, _⟩ :=
    h2fsreads_readFile_firstStop_keepSub hMm hsvc hno hPre hlrSub hFr hCodeSub hFs
  exact ⟨sfP, hUP, hStopP⟩

/-- Pure `Arm64` visited-PCs theorem for `readFile` (`0x4691b4#64`): every state `u` reached along
    `hole2_emptyProg` from `s0.setPC 0x4691b4#64` before `SubroutineStop s0` has
    `hole2_keepSub u.pc = true` (in particular `u.pc ≠ 0x468964#64`). -/
theorem h2fsreads_readFile_visited_pcs_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    ∀ u : State,
      StepsUntil hole2_emptyProg (fun x => SubroutineStop s0 x ∨ x = u)
        (s0.setPC 0x4691b4#64) u →
      ¬ SubroutineStop s0 u →
      hole2_keepSub u.pc = true := by
  have h := h2fsreads_readFile_stepsUntilInKeep_keepSub mmpl mmpl hMm hPre hFr hlrSub hCodeSub hFs
  exact h.2.1.visited_pcs h.2.2.1

/-- Scoped `StepsUntil Q` / `Steps Q` lift for `(hole2_ghFixed mpl mmpl).readFile` onto any `Q`
    agreeing with `Syscall.standard` and extern-free on `hole2_keepSub`. -/
theorem h2fsreads_readFile_ghFixed_stepsUntil_of_prog [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {Q : Program}
    (hsvc : Q.svc = Arm64.Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keepSub pc = true → Q.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readFileAnySpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem))
    (hFs : FdsGe3Closed s0.fs) :
    let hSub := f3ReadFileFixedGhostHookFineSub hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x4691b4#64 mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    let sf := hSub.val s0
    (hole2_ghFixed mpl mmpl).readFile = some hSub ∧
      h2fsalloc_StepsUntilInKeep Q hole2_keepSub (SubroutineStop s0)
        (s0.setPC 0x4691b4#64) sf ∧
      StepsUntil Q (SubroutineStop s0) (s0.setPC 0x4691b4#64) sf ∧
      Steps Q (s0.setPC 0x4691b4#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      FdsGe3Closed sf.fs ∧
      ExecFrozen sf.mem := by
  obtain ⟨hField, hIn, hStop, hFsEq, hTrEq, hFsT, hFsSf, hFrSf⟩ :=
    h2fsreads_readFile_stepsUntilInKeep_keepSub mpl mmpl hMm hPre hFr hlrSub hCodeSub hFs
  have hInQ := hIn.liftProg hsvc.symm (fun _ _ => rfl) hno_ext
  exact ⟨hField, hInQ, hInQ.toStepsUntil, hInQ.toSteps, hStop, hFsEq, hTrEq, hFsT, hFsSf, hFrSf⟩

/-- Real first-stop run of `signal_session_io::read_stdin` (`0x469000#64`) directly from
`hole2_keepSub` premises. -/
theorem h2fsreads_readStdin_firstStop_keepSub [LibsignalPlacement]
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hno : ∀ pc, hole2_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC 0x469000#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, ⟨x, st⟩, R, hSatB⟩ := hPre
  have hSatC := h2fsreads_pre_compiled_of_bounded hSatB
  have hKeepMng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true :=
    h2fsreads_keepSub_mallocng mmpl hMm
  obtain ⟨sf, huntil, hstop, _, hfiles, htr_eq, hfds, hfr_sf⟩ :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.real_readStdin_run_of_stripS
      hsvc LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      hno LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (fun st' s' =>
        LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.fineHookRustCliAllocBudget_pool_stripS
          γ mmpl tp cliElfImage.brkStart hKeepMng cliBudgetLimits st' s')
      (h2fsreads_readStdinCond_ok mmpl hMm γ tp)
      hRun hSp hSatC hFr hlrSub hCodeSub
  exact ⟨sf, huntil, hstop, hfiles, htr_eq, FsTraced.of_eq htr_eq hfiles, hfds, hfr_sf⟩

/-- `ActiveReadStdinLinkedRun` on `(hole2_keepSub, hole2_emptyProg)` under `hole2_keepSub`
premises. -/
theorem h2fsreads_readStdin_activeRealRun_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ActiveReadStdinLinkedRun hole2_keepSub hole2_emptyProg f3TrialRxProg 0x469000#64 s0 := by
  obtain ⟨sf, huntil, hstop, hfiles, htr_eq, _, hfds, hfr_sf⟩ :=
    h2fsreads_readStdin_firstStop_keepSub (P := hole2_emptyProg) hMm rfl (fun _ _ => rfl)
      hPre hlrSub hFr hCodeSub
  exact ⟨hFr, hlrSub, hCodeSub, sf, huntil, hstop, hfiles, htr_eq, hfds, hfr_sf⟩

/-- `h2fsalloc_StepsUntilInKeep` witness in `hole2_keepSub` for `(hole2_ghFixed mpl mmpl).readStdin`. -/
theorem h2fsreads_readStdin_stepsUntilInKeep_keepSub [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    let hSub := f3ReadStdinGhostHookFineSub hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x469000#64 mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    let sf := hSub.val s0
    (hole2_ghFixed mpl mmpl).readStdin = some hSub ∧
      h2fsalloc_StepsUntilInKeep hole2_emptyProg hole2_keepSub (SubroutineStop s0)
        (s0.setPC 0x469000#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      ExecFrozen sf.mem := by
  classical
  have hReal : ActiveReadStdinLinkedRun hole2_keepSub hole2_emptyProg f3TrialRxProg 0x469000#64 s0 :=
    h2fsreads_readStdin_activeRealRun_keepSub mmpl hMm hPre hFr hlrSub hCodeSub
  have hActPre :
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.ActiveF3ReadStdinPre
        (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack s0 := hPre
  have heq : (f3ReadStdinGhostHookFineSub hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x469000#64 mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack).val s0 =
      Classical.choose hReal.2.2.2 := by
    change LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHook
      hole2_keepSub hole2_emptyProg f3TrialRxProg 0x469000#64
      (fun γ tp => fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      cliBudgetLimits hole2_hookStack _ s0 = _
    unfold LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHook
    simp only [hActPre, hReal, ↓reduceDIte]
  obtain ⟨hU0, hStop, hFiles, hTrEq, hFds, hFrSf⟩ := Classical.choose_spec hReal.2.2.2
  dsimp only
  rw [heq]
  refine ⟨rfl, ?_, hStop, hFiles, hTrEq, FsTraced.of_eq hTrEq hFiles, hFds, hFrSf⟩
  refine h2fsalloc_stepsUntilInKeep_of_allProg (fun P hsvc hno => ?_) hU0
  obtain ⟨sfP, hUP, hStopP, _, _, _, _, _⟩ :=
    h2fsreads_readStdin_firstStop_keepSub hMm hsvc hno hPre hlrSub hFr hCodeSub
  exact ⟨sfP, hUP, hStopP⟩

/-- Pure `Arm64` visited-PCs theorem for `readStdin` (`0x469000#64`): every state `u` reached along
    `hole2_emptyProg` from `s0.setPC 0x469000#64` before `SubroutineStop s0` has
    `hole2_keepSub u.pc = true` (in particular `u.pc ≠ 0x468964#64`). -/
theorem h2fsreads_readStdin_visited_pcs_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ∀ u : State,
      StepsUntil hole2_emptyProg (fun x => SubroutineStop s0 x ∨ x = u)
        (s0.setPC 0x469000#64) u →
      ¬ SubroutineStop s0 u →
      hole2_keepSub u.pc = true := by
  have h := h2fsreads_readStdin_stepsUntilInKeep_keepSub mmpl mmpl hMm hPre hFr hlrSub hCodeSub
  exact h.2.1.visited_pcs h.2.2.1

/-- Scoped `StepsUntil Q` / `Steps Q` lift for `(hole2_ghFixed mpl mmpl).readStdin` onto any `Q`
    agreeing with `Syscall.standard` and extern-free on `hole2_keepSub`. -/
theorem h2fsreads_readStdin_ghFixed_stepsUntil_of_prog [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {Q : Program}
    (hsvc : Q.svc = Arm64.Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keepSub pc = true → Q.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre
      (fun γ tp => readStdinSpecOfPlaced cliIo
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack ReadStdinBoundedEnv) s0)
    (hFr : ExecFrozen s0.mem)
    (hlrSub : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCodeSub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    let hSub := f3ReadStdinGhostHookFineSub hole2_keepSub hole2_emptyProg f3TrialRxProg
      0x469000#64 mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
    let sf := hSub.val s0
    (hole2_ghFixed mpl mmpl).readStdin = some hSub ∧
      h2fsalloc_StepsUntilInKeep Q hole2_keepSub (SubroutineStop s0)
        (s0.setPC 0x469000#64) sf ∧
      StepsUntil Q (SubroutineStop s0) (s0.setPC 0x469000#64) sf ∧
      Steps Q (s0.setPC 0x469000#64) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs.files = s0.fs.files ∧
      sf.trace = s0.trace ∧
      FsTraced IsFsC s0 sf ∧
      (FdsGe3Closed s0.fs → FdsGe3Closed sf.fs) ∧
      ExecFrozen sf.mem := by
  obtain ⟨hField, hIn, hStop, hFiles, hTrEq, hFsT, hFds, hFrSf⟩ :=
    h2fsreads_readStdin_stepsUntilInKeep_keepSub mpl mmpl hMm hPre hFr hlrSub hCodeSub
  have hInQ := hIn.liftProg hsvc.symm (fun _ _ => rfl) hno_ext
  exact ⟨hField, hInQ, hInQ.toStepsUntil, hInQ.toSteps, hStop, hFiles, hTrEq, hFsT, hFds, hFrSf⟩


end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopReads
