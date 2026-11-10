/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryProof
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs
import LibsignalBinary.Proofs.E2E.Bin.Tpidr
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Main.MuslHarnessOk
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliSymtabGhost
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Process Out-of-Memory Bridge and Session-Mode Composition

Whole-process OOM disjunction bridges from `mainSpecTight` to `CliRunsTo` and `cliRunAbortOnPanic`,
preserving `allocFailedEvent` traces across `toSigState` (`SIGABRT`), together with parametric
extern-table (`Ext`) session-mode composition.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession.MuslElf

/-! ## Tight `main` Contract and `outcome_of_main_tight` -/

/-- Tight `main` contract routing allocation failure exclusively to `onPanic` (`SIGABRT`). -/
abbrev mainSpecTight (A : RustHeap.RustAlloc) (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → Cli.RunAnswer → Prop) : Spec Cli.MainGhost :=
  Cli.mainSpecTight A img stk Statics Run

theorem subroutine_ok_mainSpec_of_tight {prog : Program} {entry_pc : BitVec 64}
    {A : RustHeap.RustAlloc} {img : Obj.Image} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (h : subroutine_ok prog entry_pc (mainSpecTight A img stk Statics Run)) :
    subroutine_ok prog entry_pc (Cli.mainSpec A img stk Statics Run) :=
  Cli.subroutine_ok_mainSpec_of_tight h

/-- Strengthened `Cli.RunAllocFails` witnessing a reachable `.Panicked` state whose trace contains `allocFailedEvent`. -/
def PanickedAllocFails (elf : ElfImage) (P : Program) (i : Inputs) : Prop :=
  ∃ s0 sf, elf.loadState (Cli.cliInputs i) = .ok s0 ∧
    Steps P s0 sf ∧ sf.status = .Panicked ∧ RustHeap.allocFailedEvent ∈ sf.trace

/-- Under `mainSpecTight`, either `outcomeOf` satisfies `MainResult.Observed` or it evaluates to `some .aborted` with `PanickedAllocFails`. -/
theorem outcome_of_main_tight {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)} {A : RustHeap.RustAlloc} {stk : Nat}
    {Statics Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img ext) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A stk Statics))
    (hG : SymtabGhost (Cli.cliProg img ext))
    (hmain : subroutine_ok (Cli.cliProg img ext) (entryOf img Cli.mainName)
      (mainSpecTight A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : Cli.MainResult} (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i)
    (hc : Cli.MainCaseB2 Run Cli.IsSendOverCap Cli.IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (Cli.cliProg img ext) (Cli.cliInputs i) = some res ∧
      Cli.MainResult.Observed i.files r res) ∨
    (outcomeOf elf (Cli.cliProg img ext) (Cli.cliInputs i) = some .aborted ∧
      PanickedAllocFails elf (Cli.cliProg img ext) i) := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := Cli.loadState_fs_trace hload
  simp only [Cli.mainEntryPre, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hFL, hsp⟩, hmem⟩ := hmem
  let sm' : State := { sm with symtab := img.symtab }
  have hpre : sm'.mem ⊨ (mainSpecTight A img stk Statics Run).pre ⟨i, r⟩ sm' ∗ Fr := by
    simp only [mainSpecTight, Cli.mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    have hentry : Cli.MainEntryFacts i sm' := by
      unfold Cli.MainEntryFacts; exact ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩
    exact ⟨⟨hFL.of_mem_eq rfl, rfl⟩, ⟨hc, hi, hentry, hsp⟩, hmem⟩
  have hcode : (Cli.cliProg img ext).CodeLoaded sm'.mem := hFL.codeLoaded_ofImage _ _
  obtain ⟨sf', hsteps1', hout, -⟩ := hmain.no_fault_before_outcome ⟨i, r⟩ Fr sm' hpc hrun hpre hal hcode
  let sf : State := { sf' with symtab := sm.symtab }
  have hsteps1 : Steps (Cli.cliProg img ext) sm sf := by
    have h := hG sm.symtab hsteps1'
    exact h
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  ·
    simp only [mainSpecTight, Cli.mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    have hret' : Returned sm sf := hret
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret' (Cli.exit_frame hstk hstk' hpost)
    have hle := hc.code_le rfl
    have hw0' : (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code := hw0
    have hfiles' : sf.fs.files = (Cli.MainPost.writeAll sm'.fs w).files := hfiles
    have hout' : ProcessOutcome.traceStreamBytes .stdout sf.trace = out := hout
    refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [Cli.MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0', Cli.signExtend_ofNat_small hle]
    · rw [htrx, hout']
    · rw [hfsx, Cli.fsView_congr hfiles']
      change fsView (Cli.MainPost.writeAll sm.fs w) = _
      rw [hfs, hfs0]
      exact Cli.fsView_writeAll_initFsState i w hc.commitOk
  ·
    simp only [mainSpecTight, Cli.mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hpan' : sf.status = .Panicked := hpan
    have habort : outcomeOf elf (Cli.cliProg img ext) (Cli.cliInputs i) = some .aborted :=
      outcomeOf_eq_aborted hload hsteps01 hpan'
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, habort, trivial⟩
    · exact Or.inr ⟨habort, ⟨s0, sf, hload, hsteps01, hpan', List.mem_of_mem_drop hA⟩⟩
  ·
    simp only [mainSpecTight, Cli.mainSpecTight, Spec.inImage, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  ·
    simp only [mainSpecTight, Cli.mainSpecTight, Spec.inImage, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem outcome_of_main_cliExterns_tight {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {stk : Nat} {Statics Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A stk Statics))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : Cli.MainResult} (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i)
    (hc : Cli.MainCaseB2 Run Cli.IsSendOverCap Cli.IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (Cli.cliProg img (cliExterns W)) (Cli.cliInputs i) = some res ∧
      Cli.MainResult.Observed i.files r res) ∨
    (outcomeOf elf (Cli.cliProg img (cliExterns W)) (Cli.cliInputs i) = some .aborted ∧
      PanickedAllocFails elf (Cli.cliProg img (cliExterns W)) i) :=
  outcome_of_main_tight hE hH (symtabGhost_ofImage_cliExterns img W) hmain hstk hstk' hi hl hc

/-! ## Trace-Preserving `toSigState` OOM Transport -/

@[simp] theorem status_cliTokenPatch (s : State) : (cliTokenPatch s).status = s.status := by
  unfold cliTokenPatch State.setMem
  rfl

theorem status_toSigState_of_panicked {s : State} (h : s.status = .Panicked) :
    (toSigState s).status = .Signaled 6 := by
  unfold toSigState sigAbrt
  simp [h, State.status_setStatus]

/-- Transports a `.Panicked` execution logging `allocFailedEvent` on `Cli.cliProg` to a `.Signaled 6` execution with identical trace on `cliProgAbortOnPanic W`. -/
theorem steps_cliProg_to_cliProgSig_toSigState_allocFailed {elf : ElfImage} {img : Obj.Image}
    {W : CliHooks} {i : Inputs} {s0 sf : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hload : elf.loadState (cliProcessInputs i) = .ok s0)
    (hsteps : Steps (Cli.cliProg img (cliExterns W)) (cliTokenPatch s0) sf)
    (hpan : sf.status = .Panicked)
    (hmem : RustHeap.allocFailedEvent ∈ sf.trace) :
    Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) (toSigState sf) ∧
      (toSigState sf).status = .Signaled 6 ∧
      RustHeap.allocFailedEvent ∈ (toSigState sf).trace := by
  rw [cliProg_ofImage_eq himg hbase W] at hsteps
  have hrun0 : (cliTokenPatch s0).status = .Running := by
    rw [status_cliTokenPatch]
    exact loadState_status_running hload
  refine ⟨steps_cliProg_to_cliProgSig hrun0 hsteps, status_toSigState_of_panicked hpan, ?_⟩
  rwa [toSigState_trace]

/-- Transports a `.Panicked` OOM execution across a `cliTokenPatch`-mapped ELF `elf'` to `cliProgAbortOnPanic W` on `elf`. -/
theorem steps_cliProg_to_cliProgSig_allocFailed_of_patch {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {i : Inputs} {s0' sf : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hload' : elf'.loadState (cliProcessInputs i) = .ok s0')
    (hsteps : Steps (Cli.cliProg img (cliExterns W)) s0' sf)
    (hpan : sf.status = .Panicked)
    (hmem : RustHeap.allocFailedEvent ∈ sf.trace) :
    ∃ s0 sf_sig,
      elf.loadState (cliProcessInputs i) = .ok s0 ∧
      s0' = cliTokenPatch s0 ∧
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) sf_sig ∧
      sf_sig.status = .Signaled 6 ∧
      RustHeap.allocFailedEvent ∈ sf_sig.trace := by
  have hload_map := hload'
  rw [hpatch] at hload_map
  cases hload : elf.loadState (cliProcessInputs i) with
  | error _ =>
    rw [hload] at hload_map
    cases hload_map
  | ok s0 =>
    rw [hload] at hload_map
    simp only [Except.map, Except.ok.injEq] at hload_map
    subst hload_map
    obtain ⟨hsteps_sig, hsig, hmem_sig⟩ :=
      steps_cliProg_to_cliProgSig_toSigState_allocFailed himg hbase hload hsteps hpan hmem
    exact ⟨s0, toSigState sf, rfl, rfl, hsteps_sig, hsig, hmem_sig⟩

/-! ## Single-Input Whole-Process OOM Disjunctions -/

/-- `CliRunsTo elf W i .aborted` (`SIGABRT`) paired with a reachable `allocFailedEvent` from `cliTokenPatch s0`. -/
def CliRunsToOomAbort (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  CliRunsTo elf W i .aborted ∧
    ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s ∧
      RustHeap.allocFailedEvent ∈ s.trace

/-- Strengthened `CliRunsToOomAbort` witnessing `s.status = .Signaled 6` at the `allocFailedEvent` state. -/
def CliRunsToOomAbortSig (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  CliRunsTo elf W i .aborted ∧
    ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s ∧
      s.status = .Signaled 6 ∧
      RustHeap.allocFailedEvent ∈ s.trace

/-- `cliRunAbortOnPanic elf W i = some .aborted` paired with a reachable `allocFailedEvent` from `cliTokenPatch s0`. -/
def CliRunOomAbort (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  cliRunAbortOnPanic elf W i = some .aborted ∧
    ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s ∧
      RustHeap.allocFailedEvent ∈ s.trace

/-- Strengthened `CliRunOomAbort` witnessing `s.status = .Signaled 6` at the `allocFailedEvent` state. -/
def CliRunOomAbortSig (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  cliRunAbortOnPanic elf W i = some .aborted ∧
    ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s ∧
      s.status = .Signaled 6 ∧
      RustHeap.allocFailedEvent ∈ s.trace

theorem CliRunsToOomAbortSig.toCliRunsToOomAbort {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (h : CliRunsToOomAbortSig elf W i) : CliRunsToOomAbort elf W i := by
  rcases h with ⟨habort, s0, s, hload, hsteps, _, hmem⟩
  exact ⟨habort, s0, s, hload, hsteps, hmem⟩

theorem CliRunsToOomAbortSig.toCliRunOomAbortSig {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (h : CliRunsToOomAbortSig elf W i) : CliRunOomAbortSig elf W i :=
  ⟨cliRunSig_eq_some h.1, h.2⟩

theorem CliRunsToOomAbort.toCliRunOomAbort {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (h : CliRunsToOomAbort elf W i) : CliRunOomAbort elf W i :=
  ⟨cliRunSig_eq_some h.1, h.2⟩

theorem CliRunOomAbortSig.toCliRunOomAbort {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (h : CliRunOomAbortSig elf W i) : CliRunOomAbort elf W i := by
  rcases h with ⟨habort, s0, s, hload, hsteps, _, hmem⟩
  exact ⟨habort, s0, s, hload, hsteps, hmem⟩

theorem cliRunsTo_or_oom_of_main_stdinOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i) :
    CliRunsTo elf W i (.exited 2 [] (filesOf i.files)) ∨ CliRunsToOomAbortSig elf W i := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := outcome_of_main_cliExterns_tight hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.stdinOverCap hstin)
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort_out, s0', sf, hload', hsteps, hpan, hmem⟩
  · rw [cliProg_ofImage_eq himg hbase W] at hout
    exact Or.inl (cliRunsTo_of_raw hpatch (cliRunsTo_of_outcomeOf_usage hout hobs))
  · rw [cliProg_ofImage_eq himg hbase W] at habort_out
    have hraw_abort : CliRunsToRaw elf' W i .aborted := cliRunsTo_of_outcomeOf habort_out
    have habort_runsTo : CliRunsTo elf W i .aborted := cliRunsTo_of_raw hpatch hraw_abort
    rw [cliInputs_eq_cliProcessInputs] at hload'
    obtain ⟨s0, sf_sig, hload, _, hsteps_sig, hsig, hmem_sig⟩ :=
      steps_cliProg_to_cliProgSig_allocFailed_of_patch himg hbase hpatch hload' hsteps hpan hmem
    exact Or.inr ⟨habort_runsTo, s0, sf_sig, hload, hsteps_sig, hsig, hmem_sig⟩

theorem cliRunsTo_or_oom_of_main_sendOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) :
    CliRunsTo elf W i (observe i.files (some none)) ∨ CliRunsToOomAbortSig elf W i := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := outcome_of_main_cliExterns_tight hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.sendOverCap hover hnstin hcoins)
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort_out, s0', sf, hload', hsteps, hpan, hmem⟩
  · rw [cliProg_ofImage_eq himg hbase W] at hout
    exact Or.inl (cliRunsTo_of_raw hpatch (cliRunsTo_of_outcomeOf_observed (a := some none) hout hobs))
  · rw [cliProg_ofImage_eq himg hbase W] at habort_out
    have hraw_abort : CliRunsToRaw elf' W i .aborted := cliRunsTo_of_outcomeOf habort_out
    have habort_runsTo : CliRunsTo elf W i .aborted := cliRunsTo_of_raw hpatch hraw_abort
    rw [cliInputs_eq_cliProcessInputs] at hload'
    obtain ⟨s0, sf_sig, hload, _, hsteps_sig, hsig, hmem_sig⟩ :=
      steps_cliProg_to_cliProgSig_allocFailed_of_patch himg hbase hpatch hload' hsteps hpan hmem
    exact Or.inr ⟨habort_runsTo, s0, sf_sig, hload, hsteps_sig, hsig, hmem_sig⟩

theorem cliRunSig_or_oom_of_main_stdinOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i) :
    cliRunAbortOnPanic elf W i = some (.exited 2 [] (filesOf i.files)) ∨ CliRunOomAbortSig elf W i := by
  rcases cliRunsTo_or_oom_of_main_stdinOverCap_tight himg hbase hE hH hmain hpatch hi hl hstin with
    hok | hoom
  · exact Or.inl (cliRunSig_eq_some hok)
  · exact Or.inr hoom.toCliRunOomAbortSig

theorem cliRunSig_or_oom_of_main_sendOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) :
    cliRunAbortOnPanic elf W i = some (observe i.files (some none)) ∨ CliRunOomAbortSig elf W i := by
  rcases cliRunsTo_or_oom_of_main_sendOverCap_tight himg hbase hE hH hmain hpatch hi hl hover hnstin
      hcoins with hok | hoom
  · exact Or.inl (cliRunSig_eq_some hok)
  · exact Or.inr hoom.toCliRunOomAbortSig

/-- Under `mainSpecTight`, any call input either satisfies `CliRunsTo elf W i (observe i.files a)` or terminates with `CliRunsToOomAbortSig elf W i`. -/
theorem cliRunsTo_or_oom_of_main_call_tight {elf elf' : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    CliRunsTo elf W i (observe i.files a) ∨ CliRunsToOomAbortSig elf W i := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := outcome_of_main_cliExterns_tight hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort_out, s0', sf, hload', hsteps, hpan, hmem⟩
  · rw [cliProg_ofImage_eq himg hbase W] at hout
    exact Or.inl (cliRunsTo_of_raw hpatch (cliRunsTo_of_outcomeOf_observed hout hobs))
  · rw [cliProg_ofImage_eq himg hbase W] at habort_out
    have hraw_abort : CliRunsToRaw elf' W i .aborted := cliRunsTo_of_outcomeOf habort_out
    have habort_runsTo : CliRunsTo elf W i .aborted := cliRunsTo_of_raw hpatch hraw_abort
    rw [cliInputs_eq_cliProcessInputs] at hload'
    obtain ⟨s0, sf_sig, hload, _, hsteps_sig, hsig, hmem_sig⟩ :=
      steps_cliProg_to_cliProgSig_allocFailed_of_patch himg hbase hpatch hload' hsteps hpan hmem
    exact Or.inr ⟨habort_runsTo, s0, sf_sig, hload, hsteps_sig, hsig, hmem_sig⟩

/-- Under `mainSpecTight`, any call input either evaluates `cliRunAbortOnPanic` to `some (observe i.files a)` or satisfies `CliRunOomAbortSig elf W i`. -/
theorem cliRunSig_or_oom_of_main_call_tight {elf elf' : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    cliRunAbortOnPanic elf W i = some (observe i.files a) ∨ CliRunOomAbortSig elf W i := by
  rcases cliRunsTo_or_oom_of_main_call_tight himg hbase hE hH hmain hpatch hi hl hrun hnover hnstin
      hcoins hcommit with hok | hoom
  · exact Or.inl (cliRunSig_eq_some hok)
  · exact Or.inr hoom.toCliRunOomAbortSig

/-! ## Session-Mode Whole-Process OOM Composition -/

/-- Tight `main`-level SM-domain functional specification (`MainOkCliSm` with `mainSpecTight`). -/
def MainOkCliSmTight (img : Obj.Image) : Prop :=
  ∀ W : CliHooks, ∃ Run : Inputs → Cli.RunAnswer → Prop,
    subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (mainSpecTight HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
    (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
      ∃ a, Run (smSendInputs g m) a ∧
        observe (smSendInputs g m).files a =
          observe (smSendInputs g m).files (smSendModel W.C g m) ∧
        Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
    (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
      ∃ a, Run (smRecvInputs g c rc) a ∧
        observe (smRecvInputs g c rc).files a =
          observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
        Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

theorem MainOkCliSmTight.toMainOkCliSm {img : Obj.Image} (h : MainOkCliSmTight img) :
    MainOkCliSm img := by
  intro W
  obtain ⟨Run, hmain, hsend, hrecv⟩ := h W
  exact ⟨Run, subroutine_ok_mainSpec_of_tight hmain, hsend, hrecv⟩

/-! ## Parametric Extern-Table (`Ext`) OOM Bridge -/

namespace ProcessOom

export ProcessBridge (cliProgWith cliProgWith_ofImage_eq step_cliProgWith_to_cliProgSigWith
  steps_cliProgWith_to_cliProgSigWith CliRunsToRawWith cliRunsToWith_of_raw
  cliRunsToWith_of_outcomeOf cliRunsToWith_of_outcomeOf_observed
  cliRunsToWith_of_outcomeOf_usage)

private theorem findSome?_const_none_oom {α β : Type} (l : List α) :
    (l.findSome? fun _ => (none : Option β)) = none := by
  induction l with | nil => rfl | cons _ _ ih => exact ih

theorem outcome_of_main_tight_ext {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)} {A : RustHeap.RustAlloc} {stk : Nat}
    {Statics Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop} (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A stk Statics))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (mainSpecTight A img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64) {i : Inputs} {r : Cli.MainResult}
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i)
    (hc : Cli.MainCaseB2 Run Cli.IsSendOverCap Cli.IsStdinOverCap i r) :
    (∃ res, outcomeOf elf (Cli.cliProg img (cliExternsWith ext)) (Cli.cliInputs i) = some res ∧
      Cli.MainResult.Observed i.files r res) ∨
    (outcomeOf elf (Cli.cliProg img (cliExternsWith ext)) (Cli.cliInputs i) = some .aborted ∧
      PanickedAllocFails elf (Cli.cliProg img (cliExternsWith ext)) i) :=
  outcome_of_main_tight hE hH hG hmain hstk hstk' hi hl hc

theorem steps_cliProgWith_to_cliProgSigWith_allocFailed_of_patch {elf elf' : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)} {i : Inputs} {s0' sf : State}
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base = cliBase)
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hload' : elf'.loadState (cliProcessInputs i) = .ok s0')
    (hsteps : Steps (Cli.cliProg img (cliExternsWith ext)) s0' sf)
    (hpan : sf.status = .Panicked) (hmem : RustHeap.allocFailedEvent ∈ sf.trace) :
    ∃ s0 sf_sig, elf.loadState (cliProcessInputs i) = .ok s0 ∧ s0' = cliTokenPatch s0 ∧
      Steps (cliProgAbortOnPanicUnderExterns ext) (cliTokenPatch s0) sf_sig ∧ sf_sig.status = .Signaled 6 ∧
      RustHeap.allocFailedEvent ∈ sf_sig.trace := by
  rw [hpatch] at hload'; cases hload : elf.loadState (cliProcessInputs i) with
  | error _ => rw [hload] at hload'; cases hload'
  | ok s0 =>
    rw [hload] at hload'; simp only [Except.map, Except.ok.injEq] at hload'; subst hload'
    rw [cliProgWith_ofImage_eq himg hbase ext] at hsteps
    have hrun0 : (cliTokenPatch s0).status = .Running := (status_cliTokenPatch _).trans (loadState_status_running hload)
    exact ⟨s0, toSigState sf, rfl, rfl, steps_cliProgWith_to_cliProgSigWith hrun0 hsteps,
      status_toSigState_of_panicked hpan, by rwa [toSigState_trace]⟩

abbrev CliRunsToOomAbortWith (elf : ElfImage) (ext : String → Option (State → State)) (i : Inputs) : Prop :=
  CliRunsToUnderExterns elf ext i .aborted ∧ CliRunAllocFailsWith elf ext i

theorem cliRunsToWith_or_oom_of_main_stdinOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i) (hstin : Cli.IsStdinOverCap i) :
    CliRunsToUnderExterns elf ext i (.exited 2 [] (filesOf i.files)) ∨ CliRunsToOomAbortWith elf ext i := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  rcases outcome_of_main_tight_ext hE hH hG hmain hstk hstk' hi hl (Cli.MainCaseB2.stdinOverCap hstin) with
    ⟨res, hout, hobs⟩ | ⟨habort_out, s0', sf, hload', hsteps, hpan, hmem⟩
  · rw [cliProgWith_ofImage_eq himg hbase ext] at hout
    exact Or.inl (cliRunsToWith_of_raw hpatch (cliRunsToWith_of_outcomeOf_usage hout hobs))
  · rw [cliProgWith_ofImage_eq himg hbase ext] at habort_out; rw [cliInputs_eq_cliProcessInputs] at hload'
    obtain ⟨s0, sf_sig, hload, _, hsteps_sig, _, hmem_sig⟩ :=
      steps_cliProgWith_to_cliProgSigWith_allocFailed_of_patch himg hbase hpatch hload' hsteps hpan hmem
    exact Or.inr ⟨cliRunsToWith_of_raw hpatch (cliRunsToWith_of_outcomeOf habort_out), s0, sf_sig, hload, hsteps_sig, hmem_sig⟩

theorem cliRunsToWith_or_oom_of_main_sendOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i) (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i) (hcoins : Cli.CoinsReadable i) :
    CliRunsToUnderExterns elf ext i (observe i.files (some none)) ∨ CliRunsToOomAbortWith elf ext i := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  rcases outcome_of_main_tight_ext hE hH hG hmain hstk hstk' hi hl
      (Cli.MainCaseB2.sendOverCap hover hnstin hcoins) with
    ⟨res, hout, hobs⟩ | ⟨habort_out, s0', sf, hload', hsteps, hpan, hmem⟩
  · rw [cliProgWith_ofImage_eq himg hbase ext] at hout
    exact Or.inl (cliRunsToWith_of_raw hpatch (cliRunsToWith_of_outcomeOf_observed (a := some none) hout hobs))
  · rw [cliProgWith_ofImage_eq himg hbase ext] at habort_out; rw [cliInputs_eq_cliProcessInputs] at hload'
    obtain ⟨s0, sf_sig, hload, _, hsteps_sig, _, hmem_sig⟩ :=
      steps_cliProgWith_to_cliProgSigWith_allocFailed_of_patch himg hbase hpatch hload' hsteps hpan hmem
    exact Or.inr ⟨cliRunsToWith_of_raw hpatch (cliRunsToWith_of_outcomeOf habort_out), s0, sf_sig, hload, hsteps_sig, hmem_sig⟩

theorem cliRunsToWith_or_oom_of_main_call_tight {elf elf' : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i) (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i) (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    CliRunsToUnderExterns elf ext i (observe i.files a) ∨ CliRunsToOomAbortWith elf ext i := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  rcases outcome_of_main_tight_ext hE hH hG hmain hstk hstk' hi hl
      (Cli.MainCaseB2.call hrun hnover hnstin hcoins hcommit) with
    ⟨res, hout, hobs⟩ | ⟨habort_out, s0', sf, hload', hsteps, hpan, hmem⟩
  · rw [cliProgWith_ofImage_eq himg hbase ext] at hout
    exact Or.inl (cliRunsToWith_of_raw hpatch (cliRunsToWith_of_outcomeOf_observed hout hobs))
  · rw [cliProgWith_ofImage_eq himg hbase ext] at habort_out; rw [cliInputs_eq_cliProcessInputs] at hload'
    obtain ⟨s0, sf_sig, hload, _, hsteps_sig, _, hmem_sig⟩ :=
      steps_cliProgWith_to_cliProgSigWith_allocFailed_of_patch himg hbase hpatch hload' hsteps hpan hmem
    exact Or.inr ⟨cliRunsToWith_of_raw hpatch (cliRunsToWith_of_outcomeOf habort_out), s0, sf_sig, hload, hsteps_sig, hmem_sig⟩

theorem cliRunsToWith_or_oom_of_guard_stdinOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {ext gExt : String → Option (State → State)} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith gExt)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hRunsTransfer : ∀ o, CliRunsToUnderExterns elf gExt i o → CliRunsToUnderExterns elf ext i o)
    (hAllocTransfer : CliRunAllocFailsWith elf gExt i → CliRunAllocFailsWith elf ext i)
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i) (hstin : Cli.IsStdinOverCap i) :
    CliRunsToUnderExterns elf ext i (.exited 2 [] (filesOf i.files)) ∨ CliRunsToOomAbortWith elf ext i := by
  rcases cliRunsToWith_or_oom_of_main_stdinOverCap_tight himg hbase hE hH hG hmain hpatch hi hl hstin with
    hok | hoom
  · exact Or.inl (hRunsTransfer _ hok)
  · exact Or.inr ⟨hRunsTransfer _ hoom.1, hAllocTransfer hoom.2⟩

theorem cliRunsToWith_or_oom_of_guard_sendOverCap_tight {elf elf' : ElfImage} {img : Obj.Image}
    {ext gExt : String → Option (State → State)} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith gExt)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hRunsTransfer : ∀ o, CliRunsToUnderExterns elf gExt i o → CliRunsToUnderExterns elf ext i o)
    (hAllocTransfer : CliRunAllocFailsWith elf gExt i → CliRunAllocFailsWith elf ext i)
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i) (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i) (hcoins : Cli.CoinsReadable i) :
    CliRunsToUnderExterns elf ext i (observe i.files (some none)) ∨ CliRunsToOomAbortWith elf ext i := by
  rcases cliRunsToWith_or_oom_of_main_sendOverCap_tight himg hbase hE hH hG hmain hpatch hi hl hover hnstin hcoins with
    hok | hoom
  · exact Or.inl (hRunsTransfer _ hok)
  · exact Or.inr ⟨hRunsTransfer _ hoom.1, hAllocTransfer hoom.2⟩

theorem cliRunsToWith_or_oom_of_guard_tight {elf elf' : ElfImage} {img : Obj.Image}
    {ext gExt : String → Option (State → State)} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith gExt)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName)
      (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hRunsTransfer : ∀ o, CliRunsToUnderExterns elf gExt i o → CliRunsToUnderExterns elf ext i o)
    (hAllocTransfer : CliRunAllocFailsWith elf gExt i → CliRunAllocFailsWith elf ext i)
    (hi : Cli.CliInputsOk i) (hl : Cli.InputsLoadable i) (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i) (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    CliRunsToUnderExterns elf ext i (observe i.files a) ∨ CliRunsToOomAbortWith elf ext i := by
  rcases cliRunsToWith_or_oom_of_main_call_tight himg hbase hE hH hG hmain hpatch hi hl hrun hnover hnstin hcoins hcommit with hok | hoom
  · exact Or.inl (hRunsTransfer _ hok)
  · exact Or.inr ⟨hRunsTransfer _ hoom.1, hAllocTransfer hoom.2⟩

private theorem supportedOn_pool_cliStatics_ext {elf : ElfImage} {img : Obj.Image}
    {A : RustHeap.RustAlloc} (hpool : emp ⊢ A.pool) (hst : CliElfStatics elf img) (hE : Cli.ElfStaticOk elf) :
    ∀ i s0, elf.loadState (Cli.cliInputs i) = .ok s0 →
      SupportedOn 0#64 (CliStaticsFootprint img) s0.mem (A.pool ∗ Cli.cliStatics img) := fun i s0 hload =>
  (hst.supportedOn_pool_cliStatics hE i s0 hload).mono (sepConj_mono_left hpool)

private theorem muslHarness_cliImg_of_elf_ext {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf) (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg) (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {A : RustHeap.RustAlloc} (hpool : emp ⊢ A.pool) (ext : String → Option (State → State)) :
    Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExternsWith ext))
      (entryOf cliImg Cli.mainName) (MuslExit.muslFiniFr elf.entry)
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg A Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)) := by
  have hE' := elfStaticOk_patchElfTokens hE
  have hend' : cliImg.base.toNat + cliImg.code.length ≤ (patchElfTokens elf).entry.toNat := by
    change cliImg.base.toNat + cliImg.code.length ≤ elf.entry.toNat
    rwa [cliImg_base, cliImg_code_length]
  exact Cli.muslHarness_ok loads_cliImg (cliExternsWith ext)
    (cliElfMusl_patchTokens hMusl hE htok hstat.disjoint) hend' hfS hfE hmainOff
    cliMainStk_le_stackBudget (hfz.frozenLoaded_patchElfTokens hE htok)
    (supportedOn_pool_cliStatics_ext hpool hstat hE') (hstat.footprint_bounds hE')

private abbrev SymtabOom := String → String → Option (BitVec 64)
private def elfSymtabOom (elf : ElfImage) : SymtabOom := fun _ name => (elf.symbols.find? (·.1 == name)).map (·.2)
private def flipSymtabOom (t : SymtabOom) : SymtabOom := fun a b => match t a b with | none => some 0#64 | some _ => none

private theorem flipSymtabOom_ne (t : SymtabOom) : flipSymtabOom t ≠ t := by
  intro h; have h0 := congrFun (congrFun h "") ""; simp only [flipSymtabOom] at h0; cases ht : t "" "" <;> simp [ht] at h0

open Classical in
private noncomputable def pinSymtabHookOom (t₀ : SymtabOom) (f : State → State) : State → State := fun s =>
  if (f (s.withSymtab t₀)).symtab = t₀ then (f (s.withSymtab t₀)).withSymtab s.symtab
  else (f (s.withSymtab t₀)).withSymtab (flipSymtabOom s.symtab)

private noncomputable def pinSymtabExtOom (t₀ : SymtabOom) (ext : String → Option (State → State)) :
    String → Option (State → State) := fun n => (ext n).map (pinSymtabHookOom t₀)

private theorem pinSymtabHookOom_tpidrEl0 (t₀ : SymtabOom) (f : State → State) (s : State) :
    (pinSymtabHookOom t₀ f s).tpidrEl0 = (f (s.withSymtab t₀)).tpidrEl0 := by
  unfold pinSymtabHookOom; by_cases h : (f (s.withSymtab t₀)).symtab = t₀ <;> simp [h] <;> rfl
private theorem pinSymtabHookOom_mem (t₀ : SymtabOom) (f : State → State) (s : State) :
    (pinSymtabHookOom t₀ f s).mem = (f (s.withSymtab t₀)).mem := by
  unfold pinSymtabHookOom; by_cases h : (f (s.withSymtab t₀)).symtab = t₀ <;> simp [h] <;> rfl
private theorem pinSymtabHookOom_fs (t₀ : SymtabOom) (f : State → State) (s : State) :
    (pinSymtabHookOom t₀ f s).fs = (f (s.withSymtab t₀)).fs := by
  unfold pinSymtabHookOom; by_cases h : (f (s.withSymtab t₀)).symtab = t₀ <;> simp [h] <;> rfl
private theorem pinSymtabHookOom_trace (t₀ : SymtabOom) (f : State → State) (s : State) :
    (pinSymtabHookOom t₀ f s).trace = (f (s.withSymtab t₀)).trace := by
  unfold pinSymtabHookOom; by_cases h : (f (s.withSymtab t₀)).symtab = t₀ <;> simp [h] <;> rfl

private theorem loadState_symtab_eq_oom {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : elf.loadState inputs = .ok s0) : s0.symtab = elfSymtabOom elf := by
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  cases hw : elf.WellFormed <;> rw [hw] at h; · cases h
  cases hd : (inputs.dirs.any fun d => hasLeadingSlash d || hasDotDot d) <;> rw [hd] at h; swap; · cases h
  cases hf : (inputs.files.any fun x => hasLeadingSlash x.1 || hasDotDot x.1 || !decide (x.2.length ≤ MAX_LFS_FILESIZE)) <;> rw [hf] at h; swap; · cases h
  cases hb : buildInitialStack elf inputs <;> rw [hb] at h <;> cases h; rfl

private theorem cliTokenPatch_symtab_oom (s : State) : (cliTokenPatch s).symtab = s.symtab := rfl

private def SpecSymtabInvariantOom {α : Type} (spec : Spec α) : Prop :=
  (∀ x s t, spec.pre x (s.withSymtab t) = spec.pre x s) ∧
  (∀ x s0 sf t0 tf, spec.post x (s0.withSymtab t0) (sf.withSymtab tf) = spec.post x s0 sf) ∧
  (∀ x s0 sf t0 tf, spec.onPanic x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onPanic x s0 sf) ∧
  (∀ x c s0 sf t0 tf, spec.onExit x c (s0.withSymtab t0) (sf.withSymtab tf) = spec.onExit x c s0 sf) ∧
  (∀ x s0 sf t0 tf, spec.onOom x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onOom x s0 sf)

private theorem subroutineOutcome_withSymtab_oom {α : Type} {spec : Spec α}
    (hinv : SpecSymtabInvariantOom spec) {x : α} {R : SepProp} {t₀ : SymtabOom} {s0 sf : State}
    (hout : SubroutineOutcome spec x R (s0.withSymtab t₀) sf) :
    SubroutineOutcome spec x R s0 (sf.withSymtab s0.symtab) := by
  have hs0 : (s0.withSymtab t₀).withSymtab s0.symtab = s0 := rfl
  have hmem : (sf.withSymtab s0.symtab).mem = sf.mem := rfl
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hex, hpost⟩ | ⟨hoom, hpost⟩
  · have hp := hinv.2.1 x (s0.withSymtab t₀) sf s0.symtab s0.symtab; rw [hs0] at hp; exact Or.inl ⟨hret, hcc, by rw [hmem, hp]; exact hpost⟩
  · have hp := hinv.2.2.1 x (s0.withSymtab t₀) sf s0.symtab s0.symtab; rw [hs0] at hp; exact Or.inr (Or.inl ⟨hpan, by rw [hmem, hp]; exact hpost⟩)
  · have hp := hinv.2.2.2.1 x c (s0.withSymtab t₀) sf s0.symtab s0.symtab; rw [hs0] at hp; exact Or.inr (Or.inr (Or.inl ⟨c, hex, by rw [hmem, hp]; exact hpost⟩))
  · have hp := hinv.2.2.2.2 x (s0.withSymtab t₀) sf s0.symtab s0.symtab; rw [hs0] at hp; exact Or.inr (Or.inr (Or.inr ⟨hoom, by rw [hmem, hp]; exact hpost⟩))

private theorem hookSat_pinSymtabExtOom {α : Type} {t₀ : SymtabOom}
    {ext : String → Option (State → State)} {name : String} {spec : Spec α}
    (hinv : SpecSymtabInvariantOom spec) (hsat : HookSat ext name spec) : HookSat (pinSymtabExtOom t₀ ext) name spec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨pinSymtabHookOom t₀ f, by simp [pinSymtabExtOom, hf], fun x R s0 hrun hpre hal => ?_⟩
  obtain ⟨hk, hsym, hout⟩ := hok x R (s0.withSymtab t₀) hrun (by rw [hinv.1 x s0 t₀]; exact hpre) hal
  have hpin : pinSymtabHookOom t₀ f s0 = (f (s0.withSymtab t₀)).withSymtab s0.symtab := by
    unfold pinSymtabHookOom; simp [hsym, State.withSymtab_symtab]
  rw [hpin]; exact ⟨hk, rfl, subroutineOutcome_withSymtab_oom hinv hout⟩

private theorem pinSymtab_lookup_cases_oom {t₀ : SymtabOom} {ext : String → Option (State → State)}
    {name : String} {f : State → State}
    (hname : Rust.withPanics (cliExternsWith (pinSymtabExtOom t₀ ext)) name = some f) :
    f = Rust.panicked ∨ ∃ g, ext name = some g ∧ f = pinSymtabHookOom t₀ g := by
  unfold Rust.withPanics cliExternsWith withCliPanics pinSymtabExtOom at hname
  split at hname; · cases hname; exact Or.inl rfl
  split at hname; · cases hname; exact Or.inl rfl
  cases hg : ext name <;> rw [hg] at hname; · cases hname
  simp only [Option.map, Option.some.injEq] at hname; exact Or.inr ⟨_, rfl, hname.symm⟩

private theorem pinSymtab_step_transport_oom {P : Program} (hsvc : SymtabFree P.svc)
    (hov : P.overrides = fun _ => none) {t₀ : SymtabOom} {ext : String → Option (State → State)}
    (hext : P.externs = Rust.withPanics (cliExternsWith (pinSymtabExtOom t₀ ext)))
    (t : SymtabOom) {s s' : State} (h : Step P s s') : Step P (s.withSymtab t) (s'.withSymtab t) := by
  cases h with
  | exec h_run h_fetch => rw [← Program.evalInst_withSymtab hsvc]; exact Step.exec (s := s.withSymtab t) h_run h_fetch
  | halt_unmapped h_run h_fetch h_ext => exact Step.halt_unmapped (s := s.withSymtab t) h_run h_fetch h_ext
  | @extern f h_run h_ext h_keep h_sym =>
    obtain ⟨name, hname⟩ := Bin.TpidrAux.findSome?_stubs_some _ _ _ ((Bin.TpidrAux.externAt?_eq_findSome? hov s.pc).symm.trans h_ext)
    rw [hext] at hname
    have hcomm : f (s.withSymtab t) = (f s).withSymtab t := by
      rcases pinSymtab_lookup_cases_oom hname with rfl | ⟨g, _, rfl⟩; · rfl
      by_cases hgt : (g (s.withSymtab t₀)).symtab = t₀
      · unfold pinSymtabHookOom; simp [hgt, State.withSymtab_withSymtab, State.withSymtab_symtab]
      · refine False.elim (flipSymtabOom_ne s.symtab (h_sym.symm.trans ?_).symm); unfold pinSymtabHookOom; simp [hgt, State.withSymtab_symtab]
    rw [← hcomm]; exact Step.extern (s := s.withSymtab t) (f := f) h_run h_ext (by rw [hcomm]; exact h_keep) (by rw [hcomm]; rfl)
  | @extern_fault f h_run h_ext h_nkeep =>
    obtain ⟨name, hname⟩ := Bin.TpidrAux.findSome?_stubs_some _ _ _ ((Bin.TpidrAux.externAt?_eq_findSome? hov s.pc).symm.trans h_ext)
    rw [hext] at hname; refine Step.extern_fault (s := s.withSymtab t) (f := f) h_run h_ext ?_
    rcases pinSymtab_lookup_cases_oom hname with rfl | ⟨g, _, rfl⟩
    · exact fun ⟨hk, _⟩ => h_nkeep ⟨hk, rfl⟩
    · by_cases hgt : (g (s.withSymtab t₀)).symtab = t₀
      · intro ⟨hk, _⟩; apply h_nkeep; rw [pinSymtabHookOom_mem] at hk ⊢; refine ⟨hk, ?_⟩; unfold pinSymtabHookOom; simp [hgt, State.withSymtab_symtab]
      · intro ⟨_, hsym'⟩; refine flipSymtabOom_ne t (hsym'.symm.trans ?_).symm; unfold pinSymtabHookOom; simp [hgt, State.withSymtab_withSymtab, State.withSymtab_symtab]

private theorem symtabGhost_ofImage_pinSymtabExtOom (img : Obj.Image) (t₀ : SymtabOom)
    (ext : String → Option (State → State)) :
    SymtabGhost (Cli.cliProg img (cliExternsWith (pinSymtabExtOom t₀ ext))) := fun t _ _ hsteps => by
  induction hsteps with
  | refl _ => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (pinSymtab_step_transport_oom execSyscall_symtabFree rfl rfl t h1) ih

private def dummyImgOom (elf : ElfImage) : Obj.Image where
  base := 0#64; code := []; dataAddr := 0#64; data := []; roData := []
  externData := elf.symbols.map fun (n, addr) => (n, addr, 0)
  gotAddr := 0#64; got := []; symbols := []; objSymbols := []; stubs := []

private theorem dummyImgOom_symtab (elf : ElfImage) : (dummyImgOom elf).symtab = elfSymtabOom elf := by
  funext _ sym; simp [Obj.Image.symtab, dummyImgOom, Obj.lookup, List.find?_map, Function.comp_def,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse, elfSymtabOom]

private theorem dummyImgOom_frozenLoaded (elf : ElfImage) (s : State) : (dummyImgOom elf).FrozenLoaded s := by
  rw [Obj.Image.frozenLoaded_iff]
  exact ⟨by simp [dummyImgOom, Program.ofImage, Program.CodeLoaded],
    by simp [dummyImgOom, Obj.Image.RoDataLoaded], by simp [dummyImgOom, Obj.Image.gotBytes, Obj.HoldsBytes]⟩

private theorem hookSat_inImage_pinSymtabExtOom {α : Type} (elf : ElfImage)
    {ext : String → Option (State → State)} {name : String} {raw : Spec α}
    (hinv : SpecSymtabInvariantOom raw) (hsat : ∀ img, HookSat ext name (raw.inImage img)) (img : Obj.Image) :
    HookSat (pinSymtabExtOom (elfSymtabOom elf) ext) name (raw.inImage img) := by
  rcases hsat (dummyImgOom elf) with ⟨f, hf, hok⟩
  refine ⟨pinSymtabHookOom (elfSymtabOom elf) f, by simp [pinSymtabExtOom, hf], fun x R s0 hrun hpre hal => ?_⟩
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : (s0.withSymtab (elfSymtabOom elf)).mem ⊨ (raw.inImage (dummyImgOom elf)).pre x (s0.withSymtab (elfSymtabOom elf)) ∗ R := by
    simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨dummyImgOom_frozenLoaded elf _, (dummyImgOom_symtab elf).symm⟩, by rw [hinv.1 x s0 (elfSymtabOom elf)]; exact hpre.2⟩
  obtain ⟨hk, hsym, hout⟩ := hok x R (s0.withSymtab (elfSymtabOom elf)) hrun hpre' hal
  have hpin : pinSymtabHookOom (elfSymtabOom elf) f s0 = (f (s0.withSymtab (elfSymtabOom elf))).withSymtab s0.symtab := by
    unfold pinSymtabHookOom; simp [hsym, State.withSymtab_symtab]
  rw [hpin]; exact ⟨hk, rfl, subroutineOutcome_withSymtab_oom hinv hout⟩

private theorem rfl_specInv {α : Type} (spec : Spec α)
    (h1 : ∀ x s t, spec.pre x (s.withSymtab t) = spec.pre x s := by intros; rfl)
    (h2 : ∀ x s0 sf t0 tf, spec.post x (s0.withSymtab t0) (sf.withSymtab tf) = spec.post x s0 sf := by intros; rfl)
    (h3 : ∀ x s0 sf t0 tf, spec.onPanic x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onPanic x s0 sf := by intros; rfl)
    (h4 : ∀ x c s0 sf t0 tf, spec.onExit x c (s0.withSymtab t0) (sf.withSymtab tf) = spec.onExit x c s0 sf := by intros; rfl)
    (h5 : ∀ x s0 sf t0 tf, spec.onOom x (s0.withSymtab t0) (sf.withSymtab tf) = spec.onOom x s0 sf := by intros; rfl) :
    SpecSymtabInvariantOom spec := ⟨h1, h2, h3, h4, h5⟩

private theorem cliExternsOk_pinSymtabExtOom {P : PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (elf : ElfImage) (hOk : CliExternsOk P A ext) :
    CliExternsOk P A (pinSymtabExtOom (elfSymtabOom elf) ext) :=
  let hs {α : Type} {n : String} {sp : Spec α} (h : SpecSymtabInvariantOom sp) (s : HookSat ext n sp) := hookSat_pinSymtabExtOom h s
  let hsi {α : Type} {n : String} {sp : Spec α} (h : SpecSymtabInvariantOom sp) (s : ∀ img, HookSat ext n (sp.inImage img)) :=
    hookSat_inImage_pinSymtabExtOom elf h s
  { tpidr := fun n f h s => by
      simp only [pinSymtabExtOom, Option.map_eq_some_iff] at h; rcases h with ⟨g, hg, rfl⟩
      rw [pinSymtabHookOom_tpidrEl0]; exact hOk.tpidr n g hg (s.withSymtab (elfSymtabOom elf)),
    noExec := fun n f h s a hx => by
      simp only [pinSymtabExtOom, Option.map_eq_some_iff] at h; rcases h with ⟨g, hg, rfl⟩
      rw [pinSymtabHookOom_mem] at hx; exact hOk.noExec n g hg (s.withSymtab (elfSymtabOom elf)) a hx,
    fsTraced := fun n f h s => by
      simp only [pinSymtabExtOom, Option.map_eq_some_iff] at h; rcases h with ⟨g, hg, rfl⟩
      rcases hOk.fsTraced n g hg (s.withSymtab (elfSymtabOom elf)) with ⟨ev, htr, hfiles⟩
      exact ⟨ev, by rw [pinSymtabHookOom_trace]; exact htr, fun hno => by rw [pinSymtabHookOom_fs]; exact hfiles hno⟩,
    fsKept := fun n f h hn s => by
      simp only [pinSymtabExtOom, Option.map_eq_some_iff] at h; rcases h with ⟨g, hg, rfl⟩
      rw [pinSymtabHookOom_fs]; exact hOk.fsKept n g hg hn (s.withSymtab (elfSymtabOom elf)),
    poolEmp := hOk.poolEmp, shim := hs (rfl_specInv _) hOk.shim,
    alloc := ⟨hs (rfl_specInv _) hOk.alloc.alloc, hs (rfl_specInv _) hOk.alloc.dealloc, hs (rfl_specInv _) hOk.alloc.realloc⟩,
    allocZeroed := hs (rfl_specInv _) hOk.allocZeroed, memset := hs (rfl_specInv _) hOk.memset,
    memmove := hs (rfl_specInv _) hOk.memmove, memcpy := hs (rfl_specInv _) hOk.memcpy,
    memcpyRO := hs (rfl_specInv _) hOk.memcpyRO, bcmp := hs (rfl_specInv _) hOk.bcmp,
    strlen := hs (rfl_specInv _) hOk.strlen, readFile := hsi (rfl_specInv _) hOk.readFile,
    writeFile := hsi (rfl_specInv _) hOk.writeFile, readStdin := hsi (rfl_specInv _) hOk.readStdin,
    writeStdout := hsi (rfl_specInv _) hOk.writeStdout, memrchr := hs (rfl_specInv _) hOk.memrchr,
    fromUtf8 := hs (rfl_specInv _) hOk.fromUtf8,
    fmtWrite := hs (rfl_specInv _) hOk.fmtWrite, formatInner := hs (rfl_specInv _) hOk.formatInner,
    durationSince := hs (rfl_specInv _) hOk.durationSince, timeAdd := hs (rfl_specInv _) hOk.timeAdd,
    blackBox := hs (rfl_specInv _) hOk.blackBox, compress256 := hs (rfl_specInv _) hOk.compress256,
    aesEnc := hs (rfl_specInv _) hOk.aesEnc, aesDec := hs (rfl_specInv _) hOk.aesDec,
    pubFromSecret := hs (rfl_specInv _) hOk.pubFromSecret, dh := hs (rfl_specInv _) hOk.dh,
    staticDrop := hs (rfl_specInv _) hOk.staticDrop, sharedDrop := hs (rfl_specInv _) hOk.sharedDrop,
    compress512 := hs (rfl_specInv _) hOk.compress512, toEdwards := hs (rfl_specInv _) hOk.toEdwards,
    compress := hs (rfl_specInv _) hOk.compress, edNeg := hs (rfl_specInv _) hOk.edNeg,
    torsionFree := hs (rfl_specInv _) hOk.torsionFree, dsmb := hs (rfl_specInv _) hOk.dsmb,
    scalarMod := hs (rfl_specInv _) hOk.scalarMod, scalarWide := hs (rfl_specInv _) hOk.scalarWide,
    kemEncaps := hs (rfl_specInv _) hOk.kemEncaps, kemDecaps := hs (rfl_specInv _) hOk.kemDecaps,
    spqr := ⟨hs (rfl_specInv _) hOk.spqr.fromSeed, hs (rfl_specInv _) hOk.spqr.pk1, hs (rfl_specInv _) hOk.spqr.pk2,
      hs (rfl_specInv _) hOk.spqr.encaps1, hs (rfl_specInv _) hOk.spqr.encaps2, hs (rfl_specInv _) hOk.spqr.decaps,
      hs (rfl_specInv _) hOk.spqr.validatePk, hs (rfl_specInv _) hOk.spqr.hmac⟩ }

private theorem cliExternsSigWith_pinOom_isSome (t₀ : SymtabOom) (ext : String → Option (State → State)) (name : String) :
    (cliExternsSigWith (pinSymtabExtOom t₀ ext) name).isSome = (cliExternsSigWith ext name).isSome := by
  unfold cliExternsSigWith cliExternsWith withCliPanics pinSymtabExtOom; split <;> [rfl; cases ext name <;> rfl]

private theorem findSome?_stubs_isSome_oom {α β : Type} (stubs : List (String × Nat))
    (X : String → Option α) (Y : String → Option β) (hdom : ∀ n, (X n).isSome = (Y n).isSome) (off : Nat) :
    (stubs.findSome? fun p => if p.2 == off then X p.1 else none).isSome =
      (stubs.findSome? fun p => if p.2 == off then Y p.1 else none).isSome := by
  induction stubs with
  | nil => rfl
  | cons p stubs ih =>
    simp only [List.findSome?_cons]; cases p.2 == off; · exact ih
    have his := hdom p.1; cases hX : X p.1 <;> cases hY : Y p.1 <;> [exact ih; simp [hX, hY] at his; simp [hX, hY] at his; rfl]

private theorem externAt?_pinOom_isSome (t₀ : SymtabOom) (ext : String → Option (State → State)) (pc : BitVec 64) :
    ((cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)).externAt? pc).isSome = ((cliProgAbortOnPanicUnderExterns ext).externAt? pc).isSome := by
  unfold cliProgAbortOnPanicUnderExterns Program.externAt? Program.hookAtOff? Program.rebase; dsimp only
  simp only [ite_self, findSome?_const_none_oom, Option.or_none]
  exact findSome?_stubs_isSome_oom _ _ _ (cliExternsSigWith_pinOom_isSome t₀ ext) _

private theorem externAt?_pinOom_eq_none {t₀ : SymtabOom} {ext : String → Option (State → State)} {pc : BitVec 64} :
    (cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)).externAt? pc = none ↔ (cliProgAbortOnPanicUnderExterns ext).externAt? pc = none := by
  have his := externAt?_pinOom_isSome t₀ ext pc
  cases h1 : (cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)).externAt? pc <;>
    cases h2 : (cliProgAbortOnPanicUnderExterns ext).externAt? pc <;> simp [h1, h2] at his ⊢

private theorem fetchMem_pinOom (t₀ : SymtabOom) (ext : String → Option (State → State)) (m : Memory) (pc : BitVec 64) :
    (cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)).fetchMem m pc = (cliProgAbortOnPanicUnderExterns ext).fetchMem m pc := by
  unfold Program.fetchMem; rw [externAt?_pinOom_isSome]

private theorem findSome?_stubs_rel_oom {α β : Type} (stubs : List (String × Nat))
    (X : String → Option α) (Y : String → Option β) (hdom : ∀ n, (X n).isSome = (Y n).isSome) (off : Nat) :
    ∀ x, (stubs.findSome? fun p => if p.2 == off then X p.1 else none) = some x →
      ∃ n y, X n = some x ∧ Y n = some y ∧ (stubs.findSome? fun p => if p.2 == off then Y p.1 else none) = some y := by
  induction stubs with
  | nil => intro x hx; cases hx
  | cons p stubs ih =>
    intro x hx; simp only [List.findSome?_cons] at hx ⊢
    cases hp : p.2 == off
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hx ⊢; exact ih x hx
    · simp only [hp, ↓reduceIte] at hx ⊢; have hd := hdom p.1
      cases hX : X p.1 <;> cases hY : Y p.1
      · rw [hX] at hx; obtain ⟨n, y, hnX, hnY, hfY⟩ := ih x hx
        exact ⟨n, y, hnX, hnY, hfY⟩
      · simp [hX, hY] at hd
      · simp [hX, hY] at hd
      · rw [hX] at hx; simp only [Option.some.injEq] at hx; subst hx
        exact ⟨p.1, _, hX, hY, rfl⟩

private theorem cliExternsSigWith_pinOom_rel {t₀ : SymtabOom} {ext : String → Option (State → State)}
    {n : String} {f1 f2 : State → State} (hn1 : cliExternsSigWith (pinSymtabExtOom t₀ ext) n = some f1)
    (hn2 : cliExternsSigWith ext n = some f2) {s : State} (hsym0 : s.symtab = t₀) :
    ((f1 s).mem = (f2 s).mem) ∧ ((f1 s).symtab = s.symtab ↔ (f2 s).symtab = s.symtab) ∧
    ((f2 s).symtab = s.symtab → f1 s = f2 s) := by
  have hs_self : s.withSymtab t₀ = s := by rw [← hsym0]; rfl
  unfold cliExternsSigWith cliExternsWith withCliPanics pinSymtabExtOom at hn1
  unfold cliExternsSigWith cliExternsWith withCliPanics at hn2
  cases hpan : isCliPanicSymbol n <;> simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hn1 hn2
  · cases hg : ext n with
    | none => rw [hg] at hn1; cases hn1
    | some g =>
      rw [hg] at hn1 hn2; simp only [Option.map, Option.some.injEq] at hn1 hn2; subst hn1; subst hn2; refine ⟨?_, ?_, ?_⟩
      · rw [abortOnPanic_eq_toSigState, abortOnPanic_eq_toSigState, toSigState_mem, toSigState_mem, pinSymtabHookOom_mem, hs_self]
      · rw [abortOnPanic_eq_toSigState, abortOnPanic_eq_toSigState, toSigState_symtab, toSigState_symtab]
        by_cases hgt : (g (s.withSymtab t₀)).symtab = t₀
        · unfold pinSymtabHookOom; simp only [hgt, ↓reduceIte, State.withSymtab_symtab, true_iff]; rw [hs_self] at hgt; rw [hgt, hsym0]
        · unfold pinSymtabHookOom; simp only [hgt, ↓reduceIte, State.withSymtab_symtab]
          exact ⟨fun hbad => False.elim (flipSymtabOom_ne s.symtab hbad), fun hsym_g => False.elim (hgt (by rw [hs_self, hsym_g, hsym0]))⟩
      · intro hsym_f2; have hsym_g : (g s).symtab = s.symtab := by rwa [abortOnPanic_eq_toSigState, toSigState_symtab] at hsym_f2
        have hgt : (g (s.withSymtab t₀)).symtab = t₀ := by rw [hs_self, hsym_g, hsym0]
        have hpin : pinSymtabHookOom t₀ g s = g s := by unfold pinSymtabHookOom; simp only [hgt, ↓reduceIte]; rw [hs_self, ← hsym_g]; rfl
        rw [abortOnPanic_eq_toSigState, abortOnPanic_eq_toSigState, hpin]
  · simp only [Option.map, Option.some.injEq] at hn1 hn2; subst hn1; subst hn2; exact ⟨rfl, Iff.rfl, fun _ => rfl⟩

private theorem step_pinOom_iff {t₀ : SymtabOom} {ext : String → Option (State → State)}
    {s s' : State} (hsym0 : s.symtab = t₀) :
    Step (cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)) s s' ↔ Step (cliProgAbortOnPanicUnderExterns ext) s s' := by
  have hdom := cliExternsSigWith_pinOom_isSome t₀ ext
  have hov1 : (cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)).overrides = fun _ => none := rfl
  have hov2 : (cliProgAbortOnPanicUnderExterns ext).overrides = fun _ => none := rfl
  constructor <;> intro h <;> cases h
  · exact Step.exec ‹_› ((fetchMem_pinOom t₀ ext s.mem s.pc).symm.trans ‹_›)
  · exact Step.halt_unmapped ‹_› ((fetchMem_pinOom t₀ ext s.mem s.pc).symm.trans ‹_›) (externAt?_pinOom_eq_none.mp ‹_›)
  · rename_i f1 h_run h_ext h_keep h_sym
    obtain ⟨n, f2, hn1, hn2, hf2⟩ := findSome?_stubs_rel_oom _ _ _ hdom _ f1 ((Bin.TpidrAux.externAt?_eq_findSome? hov1 s.pc).symm.trans h_ext)
    obtain ⟨_, hsym_iff, heq_f⟩ := cliExternsSigWith_pinOom_rel hn1 hn2 hsym0
    have hsym2 := hsym_iff.mp h_sym; rw [heq_f hsym2] at h_keep ⊢
    exact Step.extern h_run ((Bin.TpidrAux.externAt?_eq_findSome? hov2 s.pc).trans hf2) h_keep hsym2
  · rename_i f1 h_run h_ext h_nkeep
    obtain ⟨n, f2, hn1, hn2, hf2⟩ := findSome?_stubs_rel_oom _ _ _ hdom _ f1 ((Bin.TpidrAux.externAt?_eq_findSome? hov1 s.pc).symm.trans h_ext)
    obtain ⟨hmem_eq, hsym_iff, _⟩ := cliExternsSigWith_pinOom_rel hn1 hn2 hsym0
    exact Step.extern_fault h_run ((Bin.TpidrAux.externAt?_eq_findSome? hov2 s.pc).trans hf2) (fun ⟨hk, hs⟩ => h_nkeep ⟨by rwa [hmem_eq], hsym_iff.mpr hs⟩)
  · exact Step.exec ‹_› ((fetchMem_pinOom t₀ ext s.mem s.pc).trans ‹_›)
  · exact Step.halt_unmapped ‹_› ((fetchMem_pinOom t₀ ext s.mem s.pc).trans ‹_›) (externAt?_pinOom_eq_none.mpr ‹_›)
  · rename_i f2 h_run h_ext h_keep h_sym
    obtain ⟨n, f1, hn2, hn1, hf1⟩ := findSome?_stubs_rel_oom _ _ _ (fun n => (hdom n).symm) _ f2 ((Bin.TpidrAux.externAt?_eq_findSome? hov2 s.pc).symm.trans h_ext)
    obtain ⟨_, hsym_iff, heq_f⟩ := cliExternsSigWith_pinOom_rel hn1 hn2 hsym0
    rw [← heq_f h_sym] at h_keep ⊢
    exact Step.extern h_run ((Bin.TpidrAux.externAt?_eq_findSome? hov1 s.pc).trans hf1) h_keep (hsym_iff.mpr h_sym)
  · rename_i f2 h_run h_ext h_nkeep
    obtain ⟨n, f1, hn2, hn1, hf1⟩ := findSome?_stubs_rel_oom _ _ _ (fun n => (hdom n).symm) _ f2 ((Bin.TpidrAux.externAt?_eq_findSome? hov2 s.pc).symm.trans h_ext)
    obtain ⟨hmem_eq, hsym_iff, _⟩ := cliExternsSigWith_pinOom_rel hn1 hn2 hsym0
    exact Step.extern_fault h_run ((Bin.TpidrAux.externAt?_eq_findSome? hov1 s.pc).trans hf1) (fun ⟨hk, hs⟩ => h_nkeep ⟨by rwa [← hmem_eq], hsym_iff.mp hs⟩)

private theorem steps_pinOom_iff {t₀ : SymtabOom} {ext : String → Option (State → State)} {s sf : State} (hsym0 : s.symtab = t₀) :
    Steps (cliProgAbortOnPanicUnderExterns (pinSymtabExtOom t₀ ext)) s sf ↔ Steps (cliProgAbortOnPanicUnderExterns ext) s sf := by
  constructor <;> intro h <;> induction h with
  | refl _ => exact Steps.refl _
  | step h1 _ ih =>
    first
    | exact Steps.step ((step_pinOom_iff hsym0).mp h1) (ih (h1.symtab_eq.trans hsym0))
    | exact Steps.step ((step_pinOom_iff hsym0).mpr h1) (ih (h1.symtab_eq.trans hsym0))

private theorem cliRunsToWith_pinOom_mp {elf : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs} {o : Outcome} (h : CliRunsToUnderExterns elf (pinSymtabExtOom (elfSymtabOom elf) ext) i o) : CliRunsToUnderExterns elf ext i o := by
  rcases h with ⟨s0, hload, ⟨out, ⟨sf, hst, hterm⟩, hobs⟩ | ⟨_, _, _, hfalse⟩, hsafe⟩
  · have hsym : (cliTokenPatch s0).symtab = elfSymtabOom elf := (cliTokenPatch_symtab_oom s0).trans (loadState_symtab_eq_oom hload)
    refine ⟨s0, hload, Or.inl ⟨out, ⟨sf, (steps_pinOom_iff hsym).mp hst, hterm⟩, hobs⟩, fun s' hst' => ?_⟩
    rcases hsafe s' ((steps_pinOom_iff hsym).mpr hst') with ht | hoom | ⟨hrun, s'', hstep⟩
    · exact Or.inl ht
    · exact Or.inr (Or.inl hoom)
    · exact Or.inr (Or.inr ⟨hrun, s'', (step_pinOom_iff (hst'.symtab_eq.trans hsym)).mp hstep⟩)
  · exact False.elim hfalse

private theorem cliRunAllocFailsWith_pinOom_mp {elf : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs} (h : CliRunAllocFailsWith elf (pinSymtabExtOom (elfSymtabOom elf) ext) i) : CliRunAllocFailsWith elf ext i := by
  rcases h with ⟨s0, s, hload, hst, hmem⟩
  exact ⟨s0, s, hload, (steps_pinOom_iff ((cliTokenPatch_symtab_oom s0).trans (loadState_symtab_eq_oom hload))).mp hst, hmem⟩

/-! ### Session-Mode `Ext` Composers -/

abbrev MainOkCliSmTightExt (img : Obj.Image) : Prop :=
  ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)), CliExternsOk P A ext →
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
        (mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a = observe (smSendInputs g m).files (smSendModel P.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a = observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

abbrev CliBinaryOrOomExt (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)), CliExternsOk P A ext →
    (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
      CliRunsToUnderExterns elf ext (smSendInputs g m)
        (if m.length > stdinCapBytes then
          .exited 2 [] (filesOf (smSendInputs g m).files)
        else if m.length > maxPlaintextBytes then
          .exited 1 [] (filesOf (smSendInputs g m).files)
        else
          observe (smSendInputs g m).files (smSendModel P.C g m)) ∨
      CliRunsToOomAbortWith elf ext (smSendInputs g m)) ∧
    (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
      CliRunsToUnderExterns elf ext (smRecvInputs g c rc)
        (if (msgTypeWhisper :: c).length > stdinCapBytes then
          .exited 2 [] (filesOf (smRecvInputs g c rc).files)
        else
          observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc)) ∨
      CliRunsToOomAbortWith elf ext (smRecvInputs g c rc))

theorem cliBinaryCorrectExt_of_orOom {elf : ElfImage} (h : CliBinaryOrOomExt elf) : CliBinaryCorrectExt elf :=
  ⟨h.1, fun P A ext hOk halloc =>
    ⟨fun g m hg hm => (h.2 P A ext hOk).1 g m hg hm |>.resolve_right fun ⟨_, s0, s, hl, hs, hm'⟩ => halloc.1 g m hg hm s0 s hl hs hm',
     fun g c rc hg hc => (h.2 P A ext hOk).2 g c rc hg hc |>.resolve_right fun ⟨_, s0, s, hl, hs, hm'⟩ => halloc.2 g c rc hg hc s0 s hl hs hm'⟩⟩

theorem cliBinaryOrOomExt_of_tight {elf elf' : ElfImage} {img : Obj.Image}
    (gfn : (String → Option (State → State)) → String → Option (State → State))
    (hGuardOk : ∀ P A ext, CliExternsOk P A ext → CliExternsOk P A (gfn ext))
    (hGuardSymtab : ∀ ext, SymtabGhost (Cli.cliProg img (cliExternsWith (gfn ext))))
    (hGuardRuns : ∀ ext i o, CliRunsToUnderExterns elf (gfn ext) i o → CliRunsToUnderExterns elf ext i o)
    (hGuardAlloc : ∀ ext i, CliRunAllocFailsWith elf (gfn ext) i → CliRunAllocFailsWith elf ext i)
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base = cliBase) (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) = (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)), CliExternsOk P A ext →
      ∃ Fr : SepProp, Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i) (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : MainOkCliSmTightExt img) : CliBinaryOrOomExt elf := by
  refine ⟨hcode, fun P A ext hOk => ?_⟩
  let gExt := gfn ext; have hOk' := hGuardOk P A ext hOk
  obtain ⟨Fr, hH'⟩ := hH P A gExt hOk'; obtain ⟨Run, hmain', hsend, hrecv⟩ := hmain P A gExt hOk'
  refine ⟨fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunsToWith_or_oom_of_guard_stdinOverCap_tight himg hbase hE hH' (hGuardSymtab ext)
        hmain' (hpatch _) (hGuardRuns ext _) (hGuardAlloc ext _) (cliInputsOk_smSendInputs g m)
        (inputsLoadable_smInputs g _ _ _ hg (by decide))
        (isStdinOverCap_smSendInputs g m hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ Cli.IsStdinOverCap (smSendInputs g m) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunsToWith_or_oom_of_guard_sendOverCap_tight himg hbase hE hH' (hGuardSymtab ext)
          hmain' (hpatch _) (hGuardRuns ext _) (hGuardAlloc ext _) (cliInputsOk_smSendInputs g m)
          (inputsLoadable_smInputs g _ _ _ hg (by decide))
          (isSendOverCap_smSendInputs g m (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (Cli.coinsReadable_smInputs g (.send (partyAddress g.party.other)) [] m (by decide))
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hsend g m hg hm
        rcases cliRunsToWith_or_oom_of_guard_tight himg hbase hE hH' (hGuardSymtab ext) hmain' (hpatch _)
            (hGuardRuns ext _) (hGuardAlloc ext _) (cliInputsOk_smSendInputs g m)
            (inputsLoadable_smInputs g _ _ _ hg (by decide)) hrun
            (not_isSendOverCap_of_stdin_le (by simp only [smSendInputs, smInputs]; unfold maxPlaintextBytes at hover; omega)) hnstin
            (Cli.coinsReadable_smInputs g (.send (partyAddress g.party.other)) [] m (by decide)) hcommit with hok | hoom
        · rw [hobs] at hok; exact Or.inl hok
        · exact Or.inr hoom
  · by_cases hstin : (msgTypeWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunsToWith_or_oom_of_guard_stdinOverCap_tight himg hbase hE hH' (hGuardSymtab ext)
        hmain' (hpatch _) (hGuardRuns ext _) (hGuardAlloc ext _) (cliInputsOk_smRecvInputs g c rc)
        (inputsLoadable_smInputs g _ _ _ hg (by simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]))
        (isStdinOverCap_smRecvInputs g c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hrecv g c rc hg hc
      rcases cliRunsToWith_or_oom_of_guard_tight himg hbase hE hH' (hGuardSymtab ext) hmain' (hpatch _)
          (hGuardRuns ext _) (hGuardAlloc ext _) (cliInputsOk_smRecvInputs g c rc)
          (inputsLoadable_smInputs g _ _ _ hg (by simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE])) hrun
          (not_isSendOverCap_smRecvInputs g c rc)
          (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
          (Cli.coinsReadable_smInputs g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc)
            (msgTypeWhisper :: c) (by simp [HMAC.keyToBytes32, fileCapBytes])) hcommit with hok | hoom
      · rw [hobs] at hok; exact Or.inl hok
      · exact Or.inr hoom

/-- Segment-slice SM whole-process OOM composer under `CliExternsOk P A ext`. -/
theorem cliBinaryOrOomExt_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf) (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg) (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliSmTightExt cliImg) : CliBinaryOrOomExt elf :=
  cliBinaryOrOomExt_of_tight (pinSymtabExtOom (elfSymtabOom elf))
    (fun _ _ _ hOk => cliExternsOk_pinSymtabExtOom elf hOk)
    (fun ext => symtabGhost_ofImage_pinSymtabExtOom cliImg (elfSymtabOom elf) ext)
    (fun _ _ _ h => cliRunsToWith_pinOom_mp h) (fun _ _ h => cliRunAllocFailsWith_pinOom_mp h)
    loads_cliImg cliImg_base (hfz.codeMatches cliImg_base hE)
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i)) (elfStaticOk_patchElfTokens hE)
    (fun _ _ ext hOk => ⟨_, muslHarness_cliImg_of_elf_ext hE htok hMusl hend hfS hfE hmainOff hfz hstat hOk.poolEmp ext⟩) hmain

end ProcessOom

end CryptoVerification.SignalSession
