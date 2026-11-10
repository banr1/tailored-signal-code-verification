/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Spec.Hoare
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf

/-!
# Real-Run First-Stop Instances for `dealloc`

**Checked by Lean.**

Proves real-run first-stop obligations and `ActiveRealRun` (`f3DeallocFallback` deadness) for
`__rust_dealloc` (`f3RdlAddrs.dealloc` = `0x4694f0#64`) over `f3TrialRxProg` (`seg[2]`, `hole2_keepSub` guard).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (RustCliAllocBudgetEntries rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.Fine
  (f3RdlAddrs fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen real_subroutine_run_of_stripS specPreservesFsTrace_dealloc)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook specStripSInvariant_fine_dealloc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3TrialRxProg f3TrialRxProg_no_ext f3TrialRxProg_svc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopAlloc
  (h2fsalloc_StepsUntilInKeep h2fsalloc_keepSub_false_of_keep_false h2fsalloc_keepSub_mallocng
   h2fsalloc_keep_mallocng h2fsalloc_rdlEntries h2fsalloc_rxProg_codeLoaded_keepSub_iff_keep
   h2fsalloc_stepsUntilInKeep_of_allProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_emptyProg hole2_ghFixed hole2_keep hole2_keepSub)

/-- `(γ, tp)`-indexed fine-budget `rustCliDeallocBudgetSpec` guarding `f3DeallocGhostHookFine`
    in `hole2_ghFixed`. -/
noncomputable def h2fsdealloc_spec [LibsignalPlacement] (mmpl : MultiPlacement)
    (γ : GhostName) (tp : BitVec 64) : Spec (BitVec 64 × Nat × Nat × fineCostModel.σ) :=
  rustCliDeallocBudgetSpec fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
    cliBudgetLimits

/-- `seg[5]` entry target for `__rust_dealloc` (`__rdl_dealloc`, `0x4694f0#64`). -/
def h2fsdealloc_target : BitVec 64 :=
  f3RdlAddrs.dealloc

/-- Public `RustCliAllocBudgetEntries` bundle over `f3TrialRxProg` (`f3RdlAddrs`). -/
theorem h2fsdealloc_rdlEntries [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntries fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      f3TrialRxProg f3RdlAddrs :=
  h2fsalloc_rdlEntries mmpl hMm γ tp

/-- Compiled `f3TrialRxProg` `subroutine_ok` for `__rust_dealloc` (`f3RdlAddrs.dealloc`). -/
theorem h2fsdealloc_rdlDealloc_ok [LibsignalPlacement] (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg f3RdlAddrs.dealloc (h2fsdealloc_spec mmpl γ tp) :=
  (h2fsdealloc_rdlEntries mmpl hMm γ tp).dealloc cliBudgetLimits

private theorem h2fsdealloc_prePC [LibsignalPlacement] (mmpl : MultiPlacement)
    (γ : GhostName) (tp : BitVec 64)
    (x : BitVec 64 × Nat × Nat × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (h2fsdealloc_spec mmpl γ tp).pre x (s.setPC pc) =
      (h2fsdealloc_spec mmpl γ tp).pre x s := by
  cases s; rfl

private theorem h2fsdealloc_outPC [LibsignalPlacement] (mmpl : MultiPlacement)
    (γ : GhostName) (tp : BitVec 64)
    (x : BitVec 64 × Nat × Nat × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome (h2fsdealloc_spec mmpl γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (h2fsdealloc_spec mmpl γ tp) x R s0 sf := by
  cases s0; exact id

/-- Parametric `keep` / `P` real-run first-stop theorem for `dealloc`, proved from
    `h2fsdealloc_rdlDealloc_ok` and `real_subroutine_run_of_stripS`. -/
theorem h2fsdealloc_firstStop_of_keep [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {keep : BitVec 64 → Bool}
    (hKeepMallocng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) s0)
    (hLr : keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAddrs.dealloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS hsvc f3TrialRxProg_svc hno_ext f3TrialRxProg_no_ext
      (h2fsdealloc_rdlDealloc_ok mmpl hMm γ tp)
      (specStripSInvariant_fine_dealloc γ mmpl tp cliElfImage.brkStart hKeepMallocng
        cliBudgetLimits)
      (specPreservesFsTrace_dealloc _ cliBudgetLimits)
      (h2fsdealloc_prePC mmpl γ tp)
      (h2fsdealloc_outPC mmpl γ tp)
      hRun hSp hSat hFr hLr hCode
  exact ⟨sf, huntil, hstop, hfs, hfst, hfr_sf⟩

/-- Real-run first-stop instance for `__rust_dealloc` (`f3RdlAddrs.dealloc`, `hole2_keep`). -/
theorem h2fsdealloc_firstStop [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keep pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAddrs.dealloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsdealloc_firstStop_of_keep mmpl hMm (h2fsalloc_keep_mallocng mmpl hMm)
    hsvc hno_ext hPre hLr hFr hCode

/-- `hole2_keepSub`-scoped real-run first-stop instance for `__rust_dealloc`. -/
theorem h2fsdealloc_firstStop_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hno_ext : ∀ pc : BitVec 64, hole2_keepSub pc = true → P.externAt? pc = none)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) s0)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC f3RdlAddrs.dealloc) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsdealloc_firstStop_of_keep mmpl hMm (h2fsalloc_keepSub_mallocng mmpl hMm)
    hsvc hno_ext hPre hLr hFr hCode

/-- `ActiveRealRun` for `dealloc` (`f3RdlAddrs.dealloc`) under `hole2_keepSub` premises. -/
theorem h2fsdealloc_activeRealRun_keepSub [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) s0)
    (hFr : ExecFrozen s0.mem)
    (hLr : hole2_keepSub (s0.readReg64 .lr) = false)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.dealloc s0 :=
  ⟨hFr, hLr, hCode,
    h2fsdealloc_firstStop_keepSub mmpl hMm rfl (fun _ _ => rfl) hPre hLr hFr hCode⟩

/-- `ActiveRealRun` for `dealloc` (`f3RdlAddrs.dealloc`) under `hole2_keep` premises, making
`f3DeallocFallback` unreachable. -/
theorem h2fsdealloc_activeRealRun [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State}
    (hPre : ActiveF3CallPre (h2fsdealloc_spec mmpl) s0)
    (hLr : hole2_keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCode : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    ActiveRealRun hole2_keepSub hole2_emptyProg f3TrialRxProg f3RdlAddrs.dealloc s0 :=
  h2fsdealloc_activeRealRun_keepSub mmpl hMm hPre hFr
    (h2fsalloc_keepSub_false_of_keep_false hLr)
    ((h2fsalloc_rxProg_codeLoaded_keepSub_iff_keep s0.mem).mpr hCode)


end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopDealloc
