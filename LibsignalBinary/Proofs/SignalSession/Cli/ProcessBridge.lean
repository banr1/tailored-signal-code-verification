/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryExtProofDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Process Symbolic Bridge to `CliRunsTo` and `CliBinaryCorrect`

**Checked by Lean.**

Bridges `Cli.outcome_of_main_cliExterns` (over `Cli.cliProg img (cliExterns W)`, `.Panicked`, and
`Cli.RunAllocFails`) to `CliRunsTo elf W i o` (over `cliProgAbortOnPanic W`, where `.Panicked` maps
to `SIGABRT` via `abortOnPanic`) and `CliBinaryCorrect elf`, together with parametric extern-table
(`cliProgWith`) counterparts.

Note that `steps_cliProg_to_cliProgSig` requires `s0.status = .Running` (satisfied on loaded states
by `loadState_status_running`) so that initial states are preserved by `toSigState`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchet

/-! ## Program Alignment at `cliBase` -/

/-- At `img.base = cliBase`, `Cli.cliProg img (cliExterns W)` equals `SignalSession.cliProg W`. -/
theorem cliProg_ofImage_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (W : CliHooks) :
    Cli.cliProg img (cliExterns W) = SignalSession.cliProg W := by
  unfold Cli.cliProg SignalSession.cliProg
  rw [Program.ofImage_eq_rebase rfl himg, hbase, withPanics_cliExterns]

/-! ## Forward Step Transport to `cliProgAbortOnPanic` -/

/-- Maps `.Panicked` to `.Signaled sigAbrt` (`SIGABRT`, signal `6`), leaving all other statuses unchanged. -/
def toSigState (s : State) : State :=
  match s.status with
  | .Panicked => s.setStatus (.Signaled sigAbrt)
  | _ => s

@[simp] theorem abortOnPanic_eq_toSigState (h : State → State) (s : State) :
    abortOnPanic h s = toSigState (h s) := rfl

theorem toSigState_of_ne_panicked {s : State} (h : s.status ≠ .Panicked) :
    toSigState s = s := by
  unfold toSigState
  split
  · rename_i hp; exact absurd hp h
  · rfl

@[simp] theorem toSigState_mem (s : State) : (toSigState s).mem = s.mem := by
  unfold toSigState; split <;> rfl

@[simp] theorem toSigState_symtab (s : State) : (toSigState s).symtab = s.symtab := by
  unfold toSigState; split <;> rfl

@[simp] theorem toSigState_trace (s : State) : (toSigState s).trace = s.trace := by
  unfold toSigState; split <;> rfl

@[simp] theorem toSigState_fs (s : State) : (toSigState s).fs = s.fs := by
  unfold toSigState; split <;> rfl

private theorem findSome?_stubs_map (stubs : List (String × Nat))
    (X : String → Option (State → State)) (f : (State → State) → (State → State)) (off : Nat) :
    (stubs.findSome? fun x => if x.2 == off then (X x.1).map f else none) =
      (stubs.findSome? fun x => if x.2 == off then X x.1 else none).map f := by
  induction stubs with
  | nil => rfl
  | cons p stubs ih =>
    simp only [List.findSome?_cons]
    cases h : (p.2 == off)
    · exact ih
    · cases hX : X p.1
      · exact ih
      · rfl

private theorem findSome?_const_none {α β : Type} (l : List α) :
    (l.findSome? fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem externAt?_cliProgSig (W : CliHooks) (pc : BitVec 64) :
    (cliProgAbortOnPanic W).externAt? pc = ((SignalSession.cliProg W).externAt? pc).map abortOnPanic := by
  unfold cliProgAbortOnPanic SignalSession.cliProg Program.externAt? Program.hookAtOff? Program.rebase
    cliExternsAbortOnPanic
  dsimp only
  simp only [ite_self, findSome?_const_none, Option.or_none]
  exact findSome?_stubs_map _ _ _ _

theorem externAt?_cliProgSig_isSome (W : CliHooks) (pc : BitVec 64) :
    ((cliProgAbortOnPanic W).externAt? pc).isSome = ((SignalSession.cliProg W).externAt? pc).isSome := by
  rw [externAt?_cliProgSig]
  cases (SignalSession.cliProg W).externAt? pc <;> rfl

theorem externAt?_cliProgSig_eq_none {W : CliHooks} {pc : BitVec 64} :
    (cliProgAbortOnPanic W).externAt? pc = none ↔ (SignalSession.cliProg W).externAt? pc = none := by
  rw [externAt?_cliProgSig]
  cases (SignalSession.cliProg W).externAt? pc <;> simp

theorem fetchMem_cliProgSig (W : CliHooks) (m : Memory) (pc : BitVec 64) :
    (cliProgAbortOnPanic W).fetchMem m pc = (SignalSession.cliProg W).fetchMem m pc := by
  unfold Program.fetchMem
  rw [externAt?_cliProgSig_isSome]

theorem evalInst_cliProgSig (W : CliHooks) (inst : Instr) (s : State) :
    (cliProgAbortOnPanic W).evalInst inst s = (SignalSession.cliProg W).evalInst inst s := rfl

/-- Single-step forward transport from `SignalSession.cliProg W` to `cliProgAbortOnPanic W`. -/
theorem step_cliProg_to_cliProgSig {W : CliHooks} {s s' : State}
    (h : Step (SignalSession.cliProg W) s s') :
    Step (cliProgAbortOnPanic W) s (toSigState s') := by
  cases h with
  | @exec inst h_run h_fetch =>
    have hs_ne : s.status ≠ .Panicked := by rw [h_run]; intro hc; cases hc
    have h_ne : ((SignalSession.cliProg W).evalInst inst s).status ≠ .Panicked :=
      evalInst_standard_status_ne_panicked rfl inst hs_ne
    rw [toSigState_of_ne_panicked h_ne, ← evalInst_cliProgSig W]
    exact Step.exec h_run ((fetchMem_cliProgSig W s.mem s.pc).trans h_fetch)
  | halt_unmapped h_run h_fetch h_ext =>
    have h_ne : ({ s with status := .Halted } : State).status ≠ .Panicked := by
      intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
    exact Step.halt_unmapped h_run
      ((fetchMem_cliProgSig W s.mem s.pc).trans h_fetch)
      (externAt?_cliProgSig_eq_none.mpr h_ext)
  | @extern f h_run h_ext h_keep h_sym =>
    have h_ext_sig : (cliProgAbortOnPanic W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgSig, h_ext]; rfl
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
    have h_ext_sig : (cliProgAbortOnPanic W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgSig, h_ext]; rfl
    refine Step.extern_fault h_run h_ext_sig ?_
    rw [abortOnPanic_eq_toSigState, toSigState_mem, toSigState_symtab]
    exact h_nkeep

/-- Multi-step forward transport from `SignalSession.cliProg W` to `cliProgAbortOnPanic W` from a `.Running` state. -/
theorem steps_cliProg_to_cliProgSig {W : CliHooks} {s0 sf : State}
    (hrun0 : s0.status = .Running)
    (hsteps : Steps (SignalSession.cliProg W) s0 sf) :
    Steps (cliProgAbortOnPanic W) s0 (toSigState sf) := by
  induction hsteps with
  | refl s =>
    have h_ne : s.status ≠ .Panicked := by rw [hrun0]; intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
    exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    cases h2 with
    | refl _ =>
      exact Steps.step (step_cliProg_to_cliProgSig h1) (Steps.refl _)
    | step h2a h2b =>
      have hrun2 : s2.status = .Running := h2a.status_running
      have h_ne2 : s2.status ≠ .Panicked := by rw [hrun2]; intro hc; cases hc
      have h1' : Step (cliProgAbortOnPanic W) s1 s2 := by
        have := step_cliProg_to_cliProgSig h1
        rwa [toSigState_of_ne_panicked h_ne2] at this
      exact Steps.step h1' (ih hrun2)

/-! ## Lifting `outcomeOf` to `CliRunsTo` -/

@[simp] theorem cliInputs_eq_cliProcessInputs (i : Inputs) :
    Cli.cliInputs i = cliProcessInputs i := rfl

/-- Unpatched `ElfImageRunsTo` form of `CliRunsTo` starting directly at `s0` rather than `cliTokenPatch s0`. -/
def CliRunsToRaw (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  ElfImageRunsTo elf (cliProcessInputs i) (OutcomeMatchesProcess o)
    (oom := fun _ => False) (prog := cliProgAbortOnPanic W)

/-- Unpatched `CliAllocNeverFails` starting directly at `s0` rather than `cliTokenPatch s0`. -/
def CliAllocNeverFailsRaw (elf : ElfImage) (W : CliHooks) : Prop :=
  (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smSendInputs g m)) = .ok s0 →
      Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace) ∧
  (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams W.C) g →
    c.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smRecvInputs g c rc)) = .ok s0 →
      Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace)

/-- Transports `ElfImageRunsTo` across `elf'.loadState inputs = (elf.loadState inputs).map patch`. -/
theorem elfImageRunsTo_of_load_map {elf elf' : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {prog : Program} {patch : State → State}
    (hpatch : elf'.loadState inputs = (elf.loadState inputs).map patch)
    (hraw : ElfImageRunsTo elf' inputs post (oom := fun _ => False) (prog := prog)) :
    ∃ s0, elf.loadState inputs = .ok s0 ∧
      _root_.Arm64.Process.ProcessRunsTo prog (patch s0) post := by
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

/-- Transports `CliRunsToRaw elf'` on a token-patched ELF `elf'` back to `CliRunsTo elf` (`DEV-CLI10`). -/
theorem cliRunsTo_of_raw {elf elf' : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hraw : CliRunsToRaw elf' W i o) :
    CliRunsTo elf W i o :=
  elfImageRunsTo_of_load_map hpatch hraw

/-- Transports `CliAllocNeverFails elf W` forward to `CliAllocNeverFailsRaw elf' W` across `cliTokenPatch` (`DEV-CLI10`). -/
theorem cliAllocNeverFailsRaw_of_patch {elf elf' : ElfImage} {W : CliHooks}
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (halloc : CliAllocNeverFails elf W) :
    CliAllocNeverFailsRaw elf' W := by
  refine ⟨fun g m hg hm s0' s hload' hsteps => ?_, fun g c rc hg hc s0' s hload' hsteps => ?_⟩
  · rw [hpatch (smSendInputs g m)] at hload'
    cases hload : elf.loadState (cliProcessInputs (smSendInputs g m)) with
    | error _ => rw [hload] at hload'; cases hload'
    | ok s0 =>
      rw [hload] at hload'
      simp only [Except.map, Except.ok.injEq] at hload'
      subst hload'
      exact halloc.1 g m hg hm s0 s hload hsteps
  · rw [hpatch (smRecvInputs g c rc)] at hload'
    cases hload : elf.loadState (cliProcessInputs (smRecvInputs g c rc)) with
    | error _ => rw [hload] at hload'; cases hload'
    | ok s0 =>
      rw [hload] at hload'
      simp only [Except.map, Except.ok.injEq] at hload'
      subst hload'
      exact halloc.2 g c rc hg hc s0 s hload hsteps

/-- Lifts an `outcomeOf` witness on `SignalSession.cliProg W` to `CliRunsToRaw` on `cliProgAbortOnPanic W`. -/
theorem cliRunsTo_of_outcomeOf {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {res : ProcessResult}
    (hout : outcomeOf elf (SignalSession.cliProg W) (Cli.cliInputs i) = some res) :
    CliRunsToRaw elf W i (toOutcome res) := by
  rw [cliInputs_eq_cliProcessInputs] at hout
  obtain ⟨s0, hload, _, sf, hsteps, hres⟩ := outcomeOf_eq_some_iff.mp hout
  have hsteps_sig := steps_cliProg_to_cliProgSig (loadState_status_running hload) hsteps
  cases hst : sf.status <;> simp only [ProcessResult.ofState?, hst] at hres <;> cases hres
  ·
    rename_i code
    have heq : toSigState sf = sf :=
      toSigState_of_ne_panicked (by rw [hst]; intro hc; cases hc)
    rw [heq] at hsteps_sig
    exact ElfImageRunsTo.of_exitsWith hload
      (processExitsWith_of_exited hsteps_sig hst)
      ⟨rfl, rfl, rfl, rfl⟩
  ·
    have hsig : (toSigState sf).status = .Signaled sigAbrt := by
      simp [toSigState, hst, State.status_setStatus]
    exact ElfImageRunsTo.of_exitsWith hload
      (processExitsWith_of_signaled hsteps_sig hsig)
      ⟨rfl, rfl⟩

theorem cliRunsTo_of_outcomeOf_observed {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {a : Cli.RunAnswer} {res : ProcessResult}
    (hout : outcomeOf elf (SignalSession.cliProg W) (Cli.cliInputs i) = some res)
    (hobs : Cli.MainResult.Observed i.files (Cli.MainResult.ofAnswer a) res) :
    CliRunsToRaw elf W i (observe i.files a) := by
  rw [← Cli.MainResult.observed_ofAnswer i.files a res hobs]
  exact cliRunsTo_of_outcomeOf hout

theorem cliRunsTo_of_outcomeOf_usage {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {res : ProcessResult}
    (hout : outcomeOf elf (SignalSession.cliProg W) (Cli.cliInputs i) = some res)
    (hobs : Cli.MainResult.Observed i.files (.ret 2 [] []) res) :
    CliRunsToRaw elf W i (.exited 2 [] (filesOf i.files)) := by
  rw [← Cli.MainResult.observed_usage i.files res hobs]
  exact cliRunsTo_of_outcomeOf hout

/-! ## Allocation-Failure Contra-Lift -/

/-- Contra-lifts allocation-failure freedom from `cliProgAbortOnPanic W` back to `SignalSession.cliProg W`. -/
theorem not_runAllocFails_of_trace {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    ¬ Cli.RunAllocFails elf (SignalSession.cliProg W) i := by
  rintro ⟨s0, sf, hload, hsteps, hmem⟩
  rw [cliInputs_eq_cliProcessInputs] at hload
  have hsteps_sig := steps_cliProg_to_cliProgSig (loadState_status_running hload) hsteps
  rw [← toSigState_trace sf] at hmem
  exact hno s0 (toSigState sf) hload hsteps_sig hmem

/-! ## SM-Domain Input Side Conditions -/

theorem inputsLoadable_smInputs {C : Crypto} (g : GhostState Bytes) (cmd : Cmd)
    (coins stdin : List (BitVec 8))
    (hg : Reach (spqrOffSessionParams C) g) (hcoins : coins.length ≤ MAX_LFS_FILESIZE) :
    Cli.InputsLoadable (smInputs g cmd coins stdin) := by
  refine ⟨(loadable_smInputs g cmd coins stdin).1, fun f hf =>
    ⟨(loadable_smInputs g cmd coins stdin).2 f hf, ?_⟩⟩
  simp only [smInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · simp only [dirOfE, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · cases g.party <;> decide +kernel
    · simp [IdentityKey.serialize, PublicKey.serialize, MAX_LFS_FILESIZE]
    · have hlt := Reach.reach_encodeRecord_length_lt_20 C hg
      dsimp [MAX_LFS_FILESIZE]; omega
  · exact hcoins

theorem coinsReadable_smInputs (g : GhostState Bytes) (cmd : Cmd)
    (coins stdin : List (BitVec 8))
    (hcap : coins.length ≤ fileCapBytes := by
      first | decide | simp [HMAC.keyToBytes32, List.Vector.toList_length, initiateTapeLen, fileCapBytes]) :
    Cli.CoinsReadable (smInputs g cmd coins stdin) :=
  Cli.coinsReadable_smInputs g cmd coins stdin hcap

theorem commitOk_smSendModel (C : Crypto) (g : GhostState Bytes) (m : List (BitVec 8)) :
    Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer (smSendModel C g m)) := by
  unfold smSendModel
  cases sendModelSpqrOff C g m with
  | none => trivial
  | some r =>
    cases r with
    | none => intro _ h; cases h
    | some p =>
      rcases p with ⟨rec, _⟩
      exact Cli.writeOk_smInputs g _ _ _ rec

theorem commitOk_smRecvModel (C : Crypto) (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer (smRecvModel C g c rc)) := by
  unfold smRecvModel
  cases recvModelSpqrOff C g c rc with
  | none => trivial
  | some r =>
    cases r with
    | none => intro _ h; cases h
    | some p =>
      rcases p with ⟨rec, _⟩
      exact Cli.writeOk_smInputs g _ _ _ rec

theorem cliInputsOk_smSendInputs (g : GhostState Bytes) (m : List (BitVec 8)) :
    Cli.CliInputsOk (smSendInputs g m) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack smSendInputs smInputs
  dsimp only
  cases g.party <;> decide

theorem cliInputsOk_smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256) :
    Cli.CliInputsOk (smRecvInputs g c rc) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack smRecvInputs smInputs
  dsimp only
  cases g.party <;> decide

/-! ### Cap-Violation Helpers -/

theorem not_isSendOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ 1_000_000) :
    ¬ Cli.IsSendOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

theorem not_isStdinOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ stdinCapBytes) :
    ¬ Cli.IsStdinOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

theorem isSendOverCap_smSendInputs (g : GhostState Bytes) (m : List (BitVec 8))
    (h : 1_000_000 < m.length) :
    Cli.IsSendOverCap (smSendInputs g m) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress g.party.other)) rfl
  cases c <;> simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag
  rename_i peer
  exact ⟨peer, hc⟩

theorem isStdinOverCap_smSendInputs (g : GhostState Bytes) (m : List (BitVec 8))
    (h : stdinCapBytes < m.length) :
    Cli.IsStdinOverCap (smSendInputs g m) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress g.party.other)) rfl
  exact ⟨c, hc, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem isStdinOverCap_smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < (msgTypeWhisper :: c).length) :
    Cli.IsStdinOverCap (smRecvInputs g c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress g.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem not_isSendOverCap_smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ Cli.IsSendOverCap (smRecvInputs g c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress g.party.other)) rfl
  change Cli.MainHops.parseArgs CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
    ((Cmd.recv (partyAddress g.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag

theorem isSendOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : 1_000_000 < m.length) :
    Cli.IsSendOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  cases c <;> simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag
  rename_i peer
  exact ⟨peer, hc⟩

theorem not_isSendOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ Cli.IsSendOverCap (pqInitInputs W st b t) := by
  rintro ⟨_, hgt⟩
  simp [pqInitInputs, pqInputs] at hgt

theorem not_isSendOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ Cli.IsSendOverCap (pqRecvInputs W st c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  change Cli.MainHops.parseArgs CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
    ((Cmd.recv (partyAddress st.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag

theorem isStdinOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : stdinCapBytes < m.length) :
    Cli.IsStdinOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  exact ⟨c, hc, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem isStdinOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < c.length) :
    Cli.IsStdinOverCap (pqRecvInputs W st c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem not_isStdinOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ Cli.IsStdinOverCap (pqInitInputs W st b t) :=
  not_isStdinOverCap_of_stdin_le (by simp [pqInitInputs, pqInputs])

/-! ## Parameterized `CliBinaryCorrect` Composers -/

theorem cliRunsTo_of_main_stdinOverCap {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i)
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    CliRunsToRaw elf W i (.exited 2 [] (filesOf i.files)) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_cliExterns hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.stdinOverCap hstin)
  rw [cliProg_ofImage_eq himg hbase W] at out
  rcases out with ⟨res, hout, hobs⟩ | halloc_fail
  · exact cliRunsTo_of_outcomeOf_usage hout hobs
  · exact absurd halloc_fail (not_runAllocFails_of_trace hno)

theorem cliRunsTo_of_main_sendOverCap {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    CliRunsToRaw elf W i (observe i.files (some none)) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_cliExterns hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.sendOverCap hover hnstin hcoins)
  rw [cliProg_ofImage_eq himg hbase W] at out
  rcases out with ⟨res, hout, hobs⟩ | halloc_fail
  · exact cliRunsTo_of_outcomeOf_observed (a := some none) hout hobs
  · exact absurd halloc_fail (not_runAllocFails_of_trace hno)

theorem cliRunsTo_of_main_call {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    CliRunsToRaw elf W i (observe i.files a) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_cliExterns hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  rw [cliProg_ofImage_eq himg hbase W] at out
  rcases out with ⟨res, hout, hobs⟩ | halloc_fail
  · exact cliRunsTo_of_outcomeOf_observed hout hobs
  · exact absurd halloc_fail (not_runAllocFails_of_trace hno)

/-- Combines `CliElfCodeMatches elf`, `Cli.MuslHarness elf'` on a token-patched `elf'` (`DEV-CLI10`), and `mainSpec` with `observe`-level model agreement to establish `CliBinaryCorrect elf`. -/
theorem cliBinaryCorrect_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image}
    {A : RustHeap.RustAlloc} {Fr : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : ∀ W : CliHooks, ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))) :
    CliBinaryCorrect elf := by
  refine ⟨hcode, fun W halloc => ?_⟩
  have halloc' := cliAllocNeverFailsRaw_of_patch hpatch halloc
  obtain ⟨Run, hmainW, hsend, hrecv⟩ := hmain W
  refine ⟨fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunsTo_of_raw (hpatch (smSendInputs g m))
        (cliRunsTo_of_main_stdinOverCap himg hbase hE (hH W) hmainW
          (cliInputsOk_smSendInputs g m) (inputsLoadable_smInputs g _ _ _ hg (by decide))
          (isStdinOverCap_smSendInputs g m hstin) (halloc'.1 g m hg hm))
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ Cli.IsStdinOverCap (smSendInputs g m) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunsTo_of_raw (hpatch (smSendInputs g m))
          (cliRunsTo_of_main_sendOverCap himg hbase hE (hH W) hmainW
            (cliInputsOk_smSendInputs g m) (inputsLoadable_smInputs g _ _ _ hg (by decide))
            (isSendOverCap_smSendInputs g m (by unfold maxPlaintextBytes at hover; exact hover))
            hnstin
            (Cli.coinsReadable_smInputs g (.send (partyAddress g.party.other)) [] m (by decide))
            (halloc'.1 g m hg hm))
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hsend g m hg hm
        rw [← hobs]
        exact cliRunsTo_of_raw (hpatch (smSendInputs g m))
          (cliRunsTo_of_main_call himg hbase hE (hH W) hmainW
            (cliInputsOk_smSendInputs g m) (inputsLoadable_smInputs g _ _ _ hg (by decide))
            hrun
            (not_isSendOverCap_of_stdin_le (by simp only [smSendInputs, smInputs]; unfold maxPlaintextBytes at hover; omega))
            hnstin
            (Cli.coinsReadable_smInputs g (.send (partyAddress g.party.other)) [] m (by decide))
            hcommit
            (halloc'.1 g m hg hm))
  · by_cases hstin : (msgTypeWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunsTo_of_raw (hpatch (smRecvInputs g c rc))
        (cliRunsTo_of_main_stdinOverCap himg hbase hE (hH W) hmainW
          (cliInputsOk_smRecvInputs g c rc)
          (inputsLoadable_smInputs g _ _ _ hg (by simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]))
          (isStdinOverCap_smRecvInputs g c rc hstin) (halloc'.2 g c rc hg hc))
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hrecv g c rc hg hc
      rw [← hobs]
      exact cliRunsTo_of_raw (hpatch (smRecvInputs g c rc))
        (cliRunsTo_of_main_call himg hbase hE (hH W) hmainW
          (cliInputsOk_smRecvInputs g c rc)
          (inputsLoadable_smInputs g _ _ _ hg (by simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]))
          hrun
          (not_isSendOverCap_smRecvInputs g c rc)
          (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
          (Cli.coinsReadable_smInputs g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc)
            (msgTypeWhisper :: c) (by simp [HMAC.keyToBytes32, fileCapBytes]))
          hcommit
          (halloc'.2 g c rc hg hc))

/-- Establishes `CliBinaryCorrect elf` from `Obj.Loads`, `CliElfCodeMatches elf`, a token-patched `elf'`, `Cli.MuslHarness elf'`, and `mainSpec` on `smSendModel`/`smRecvModel`. -/
theorem cliBinaryCorrect_of_parts {elf elf' : ElfImage} {img : Obj.Image}
    {A : RustHeap.RustAlloc} {Fr : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : ∀ W : CliHooks, ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        Run (smSendInputs g m) (smSendModel W.C g m)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        Run (smRecvInputs g c rc) (smRecvModel W.C g c rc))) :
    CliBinaryCorrect elf := by
  refine cliBinaryCorrect_of_parts_observe himg hbase hcode hpatch hE hH (fun W => ?_)
  obtain ⟨Run, hmainW, hsend, hrecv⟩ := hmain W
  exact ⟨Run, hmainW,
    fun g m hg hm => ⟨_, hsend g m hg hm, rfl, commitOk_smSendModel W.C g m⟩,
    fun g c rc hg hc => ⟨_, hrecv g c rc hg hc, rfl, commitOk_smRecvModel W.C g c rc⟩⟩

/-! ## Unconditional OOM-Disjunction Process Bridge -/

/-- Unpatched allocation-failure witness on `cliProgAbortOnPanic W` starting at `s0`. -/
def CliInputAllocFailsRaw (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgAbortOnPanic W) s0 s ∧ RustHeap.allocFailedEvent ∈ s.trace

/-- Allocation-failure witness on `cliProgAbortOnPanic W` starting at `cliTokenPatch s0` (`DEV-CLI10`). -/
def CliInputAllocFails (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s ∧ RustHeap.allocFailedEvent ∈ s.trace

theorem cliInputAllocFailsRaw_of_runAllocFails {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (h : Cli.RunAllocFails elf (SignalSession.cliProg W) i) :
    CliInputAllocFailsRaw elf W i := by
  rcases h with ⟨s0, sf, hload, hsteps, hmem⟩
  rw [cliInputs_eq_cliProcessInputs] at hload
  have hsteps_sig := steps_cliProg_to_cliProgSig (loadState_status_running hload) hsteps
  exact ⟨s0, toSigState sf, hload, hsteps_sig, by rwa [toSigState_trace]⟩

theorem cliInputAllocFails_of_raw {elf elf' : ElfImage} {W : CliHooks} {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hraw : CliInputAllocFailsRaw elf' W i) :
    CliInputAllocFails elf W i := by
  rcases hraw with ⟨s0', s, hload', hsteps, hmem⟩
  rw [hpatch] at hload'
  cases hload : elf.loadState (cliProcessInputs i) with
  | error _ =>
    rw [hload] at hload'
    cases hload'
  | ok s0 =>
    rw [hload] at hload'
    simp only [Except.map, Except.ok.injEq] at hload'
    subst hload'
    exact ⟨s0, s, hload, hsteps, hmem⟩

theorem cliRunsTo_aborted_of_outcomeOf {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (hout : outcomeOf elf (SignalSession.cliProg W) (Cli.cliInputs i) = some .aborted) :
    CliRunsToRaw elf W i .aborted :=
  cliRunsTo_of_outcomeOf hout

theorem cliRunsTo_or_aborted_of_main_stdinOverCap {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i) :
    CliRunsToRaw elf W i (.exited 2 [] (filesOf i.files)) ∨
      (CliRunsToRaw elf W i .aborted ∧ CliInputAllocFailsRaw elf W i) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_cliExterns_or_oom hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.stdinOverCap hstin)
  rw [cliProg_ofImage_eq himg hbase W] at out
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort, halloc_fail⟩
  · exact Or.inl (cliRunsTo_of_outcomeOf_usage hout hobs)
  · exact Or.inr ⟨cliRunsTo_aborted_of_outcomeOf habort,
      cliInputAllocFailsRaw_of_runAllocFails halloc_fail⟩

theorem cliRunsTo_or_aborted_of_main_stdinOverCap_patch {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i) :
    CliRunsTo elf W i (.exited 2 [] (filesOf i.files)) ∨
      (CliRunsTo elf W i .aborted ∧ CliInputAllocFails elf W i) := by
  rcases cliRunsTo_or_aborted_of_main_stdinOverCap himg hbase hE hH hmain hi hl hstin with
    hraw | ⟨habort, hfail⟩
  · exact Or.inl (cliRunsTo_of_raw hpatch hraw)
  · exact Or.inr ⟨cliRunsTo_of_raw hpatch habort, cliInputAllocFails_of_raw hpatch hfail⟩

theorem cliRunsTo_or_aborted_of_main_sendOverCap {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) :
    CliRunsToRaw elf W i (observe i.files (some none)) ∨
      (CliRunsToRaw elf W i .aborted ∧ CliInputAllocFailsRaw elf W i) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_cliExterns_or_oom hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.sendOverCap hover hnstin hcoins)
  rw [cliProg_ofImage_eq himg hbase W] at out
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort, halloc_fail⟩
  · exact Or.inl (cliRunsTo_of_outcomeOf_observed (a := some none) hout hobs)
  · exact Or.inr ⟨cliRunsTo_aborted_of_outcomeOf habort,
      cliInputAllocFailsRaw_of_runAllocFails halloc_fail⟩

theorem cliRunsTo_or_aborted_of_main_sendOverCap_patch {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) :
    CliRunsTo elf W i (observe i.files (some none)) ∨
      (CliRunsTo elf W i .aborted ∧ CliInputAllocFails elf W i) := by
  rcases cliRunsTo_or_aborted_of_main_sendOverCap himg hbase hE hH hmain hi hl hover hnstin hcoins with
    hraw | ⟨habort, hfail⟩
  · exact Or.inl (cliRunsTo_of_raw hpatch hraw)
  · exact Or.inr ⟨cliRunsTo_of_raw hpatch habort, cliInputAllocFails_of_raw hpatch hfail⟩

/-- Single-call raw OOM-disjunction bridge from `Cli.mainSpecTight`: either the process runs to `observe i.files a` or it aborts (`SIGABRT`) with `CliInputAllocFailsRaw`. -/
theorem cliRunsTo_or_aborted_of_main_call {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    CliRunsToRaw elf W i (observe i.files a) ∨
      (CliRunsToRaw elf W i .aborted ∧ CliInputAllocFailsRaw elf W i) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_cliExterns_or_oom hE hH hmain hstk hstk' hi hl
    (Cli.MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  rw [cliProg_ofImage_eq himg hbase W] at out
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort, halloc_fail⟩
  · exact Or.inl (cliRunsTo_of_outcomeOf_observed hout hobs)
  · exact Or.inr ⟨cliRunsTo_aborted_of_outcomeOf habort,
      cliInputAllocFailsRaw_of_runAllocFails halloc_fail⟩

/-- Token-patched single-call OOM-disjunction bridge from `Cli.mainSpecTight`. -/
theorem cliRunsTo_or_aborted_of_main_call_patch {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
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
    CliRunsTo elf W i (observe i.files a) ∨
      (CliRunsTo elf W i .aborted ∧ CliInputAllocFails elf W i) := by
  rcases cliRunsTo_or_aborted_of_main_call himg hbase hE hH hmain hi hl hrun hnover hnstin hcoins hcommit with
    hraw | ⟨habort, hfail⟩
  · exact Or.inl (cliRunsTo_of_raw hpatch hraw)
  · exact Or.inr ⟨cliRunsTo_of_raw hpatch habort, cliInputAllocFails_of_raw hpatch hfail⟩

/-! ## Parametric Extern-Table (`cliProgWith`) Process Bridge -/

namespace ProcessBridge

/-- Rebased CLI program parameterized by an arbitrary extern table `ext` (prior to `abortOnPanic`). -/
noncomputable def cliProgWith (ext : String → Option (State → State)) : Program :=
  libsignalSessionImage.toProgram.rebase cliBase (cliExternsWith ext)

theorem cliProg_eq_cliProgWith (W : CliHooks) :
    SignalSession.cliProg W = cliProgWith (cliHookExterns W) := rfl

theorem cliProgWith_ofImage_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase) (ext : String → Option (State → State)) :
    Cli.cliProg img (cliExternsWith ext) = cliProgWith ext := by
  unfold Cli.cliProg cliProgWith cliExternsWith
  rw [Program.ofImage_eq_rebase rfl himg, hbase, withPanics_withCliPanics]

private theorem findSome?_stubs_map_with (stubs : List (String × Nat))
    (X : String → Option (State → State)) (f : (State → State) → (State → State)) (off : Nat) :
    (stubs.findSome? fun x => if x.2 == off then (X x.1).map f else none) =
      (stubs.findSome? fun x => if x.2 == off then X x.1 else none).map f := by
  induction stubs with
  | nil => rfl
  | cons p stubs ih =>
    simp only [List.findSome?_cons]
    cases h : (p.2 == off)
    · exact ih
    · cases hX : X p.1
      · exact ih
      · rfl

private theorem findSome?_const_none_with {α β : Type} (l : List α) :
    (l.findSome? fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem externAt?_cliProgSigWith (ext : String → Option (State → State)) (pc : BitVec 64) :
    (cliProgAbortOnPanicUnderExterns ext).externAt? pc = ((cliProgWith ext).externAt? pc).map abortOnPanic := by
  unfold cliProgAbortOnPanicUnderExterns cliProgWith Program.externAt? Program.hookAtOff? Program.rebase
    cliExternsSigWith
  dsimp only
  simp only [ite_self, findSome?_const_none_with, Option.or_none]
  exact findSome?_stubs_map_with _ _ _ _

theorem externAt?_cliProgSigWith_isSome (ext : String → Option (State → State)) (pc : BitVec 64) :
    ((cliProgAbortOnPanicUnderExterns ext).externAt? pc).isSome = ((cliProgWith ext).externAt? pc).isSome := by
  rw [externAt?_cliProgSigWith]
  cases (cliProgWith ext).externAt? pc <;> rfl

theorem externAt?_cliProgSigWith_eq_none {ext : String → Option (State → State)} {pc : BitVec 64} :
    (cliProgAbortOnPanicUnderExterns ext).externAt? pc = none ↔ (cliProgWith ext).externAt? pc = none := by
  rw [externAt?_cliProgSigWith]
  cases (cliProgWith ext).externAt? pc <;> simp

theorem fetchMem_cliProgSigWith (ext : String → Option (State → State))
    (m : Memory) (pc : BitVec 64) :
    (cliProgAbortOnPanicUnderExterns ext).fetchMem m pc = (cliProgWith ext).fetchMem m pc := by
  unfold Program.fetchMem
  rw [externAt?_cliProgSigWith_isSome]

theorem evalInst_cliProgSigWith (ext : String → Option (State → State))
    (inst : Instr) (s : State) :
    (cliProgAbortOnPanicUnderExterns ext).evalInst inst s = (cliProgWith ext).evalInst inst s := rfl

theorem step_cliProgWith_to_cliProgSigWith {ext : String → Option (State → State)} {s s' : State}
    (h : Step (cliProgWith ext) s s') :
    Step (cliProgAbortOnPanicUnderExterns ext) s (toSigState s') := by
  cases h with
  | @exec inst h_run h_fetch =>
    have hs_ne : s.status ≠ .Panicked := by rw [h_run]; intro hc; cases hc
    have h_ne : ((cliProgWith ext).evalInst inst s).status ≠ .Panicked :=
      evalInst_standard_status_ne_panicked rfl inst hs_ne
    rw [toSigState_of_ne_panicked h_ne, ← evalInst_cliProgSigWith ext]
    exact Step.exec h_run ((fetchMem_cliProgSigWith ext s.mem s.pc).trans h_fetch)
  | halt_unmapped h_run h_fetch h_ext =>
    have h_ne : ({ s with status := .Halted } : State).status ≠ .Panicked := by
      intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
    exact Step.halt_unmapped h_run
      ((fetchMem_cliProgSigWith ext s.mem s.pc).trans h_fetch)
      (externAt?_cliProgSigWith_eq_none.mpr h_ext)
  | @extern f h_run h_ext h_keep h_sym =>
    have h_ext_sig : (cliProgAbortOnPanicUnderExterns ext).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgSigWith, h_ext]; rfl
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
    have h_ext_sig : (cliProgAbortOnPanicUnderExterns ext).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgSigWith, h_ext]; rfl
    refine Step.extern_fault h_run h_ext_sig ?_
    rw [abortOnPanic_eq_toSigState, toSigState_mem, toSigState_symtab]
    exact h_nkeep

theorem steps_cliProgWith_to_cliProgSigWith {ext : String → Option (State → State)} {s0 sf : State}
    (hrun0 : s0.status = .Running)
    (hsteps : Steps (cliProgWith ext) s0 sf) :
    Steps (cliProgAbortOnPanicUnderExterns ext) s0 (toSigState sf) := by
  induction hsteps with
  | refl s =>
    have h_ne : s.status ≠ .Panicked := by rw [hrun0]; intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
    exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    cases h2 with
    | refl _ =>
      exact Steps.step (step_cliProgWith_to_cliProgSigWith h1) (Steps.refl _)
    | step h2a _ =>
      have hrun2 : s2.status = .Running := h2a.status_running
      have h_ne2 : s2.status ≠ .Panicked := by rw [hrun2]; intro hc; cases hc
      have h1' : Step (cliProgAbortOnPanicUnderExterns ext) s1 s2 := by
        have := step_cliProgWith_to_cliProgSigWith h1
        rwa [toSigState_of_ne_panicked h_ne2] at this
      exact Steps.step h1' (ih hrun2)

/-- Unpatched `ElfImageRunsTo` form of `CliRunsToUnderExterns`. -/
def CliRunsToRawWith (elf : ElfImage) (ext : String → Option (State → State))
    (i : Inputs) (o : Outcome) : Prop :=
  ElfImageRunsTo elf (cliProcessInputs i) (OutcomeMatchesProcess o)
    (oom := fun _ => False) (prog := cliProgAbortOnPanicUnderExterns ext)

/-- Unpatched `CliAllocNeverFailsWith`. -/
def CliAllocNeverFailsRawWith (elf : ElfImage) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  (∀ (g : GhostState Bytes) (m : List (BitVec 8)), Reach (spqrOffSessionParams C) g → m.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smSendInputs g m)) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) s0 s → RustHeap.allocFailedEvent ∉ s.trace) ∧
  (∀ (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256), Reach (spqrOffSessionParams C) g →
    c.length < 2 ^ 32 →
    ∀ s0 s, elf.loadState (cliProcessInputs (smRecvInputs g c rc)) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) s0 s → RustHeap.allocFailedEvent ∉ s.trace)

theorem cliRunsToWith_of_raw {elf elf' : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs} {o : Outcome}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hraw : CliRunsToRawWith elf' ext i o) :
    CliRunsToUnderExterns elf ext i o :=
  elfImageRunsTo_of_load_map hpatch hraw

theorem cliAllocNeverFailsRawWith_of_patch {elf elf' : ElfImage} {C : Crypto}
    {ext : String → Option (State → State)}
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (halloc : CliAllocNeverFailsWith elf C ext) :
    CliAllocNeverFailsRawWith elf' C ext := by
  refine ⟨fun g m hg hm s0' s hload' hsteps => ?_, fun g c rc hg hc s0' s hload' hsteps => ?_⟩
  · rw [hpatch (smSendInputs g m)] at hload'
    cases hload : elf.loadState (cliProcessInputs (smSendInputs g m)) with
    | error _ => rw [hload] at hload'; cases hload'
    | ok s0 =>
      rw [hload] at hload'
      simp only [Except.map, Except.ok.injEq] at hload'
      subst hload'
      exact halloc.1 g m hg hm s0 s hload hsteps
  · rw [hpatch (smRecvInputs g c rc)] at hload'
    cases hload : elf.loadState (cliProcessInputs (smRecvInputs g c rc)) with
    | error _ => rw [hload] at hload'; cases hload'
    | ok s0 =>
      rw [hload] at hload'
      simp only [Except.map, Except.ok.injEq] at hload'
      subst hload'
      exact halloc.2 g c rc hg hc s0 s hload hsteps

theorem cliRunsToWith_of_outcomeOf {elf : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs} {res : ProcessResult}
    (hout : outcomeOf elf (cliProgWith ext) (Cli.cliInputs i) = some res) :
    CliRunsToRawWith elf ext i (toOutcome res) := by
  rw [cliInputs_eq_cliProcessInputs] at hout
  obtain ⟨s0, hload, _, sf, hsteps, hres⟩ := outcomeOf_eq_some_iff.mp hout
  have hsteps_sig := steps_cliProgWith_to_cliProgSigWith (loadState_status_running hload) hsteps
  cases hst : sf.status <;> simp only [ProcessResult.ofState?, hst] at hres <;> cases hres
  · rename_i code
    have heq : toSigState sf = sf :=
      toSigState_of_ne_panicked (by rw [hst]; intro hc; cases hc)
    rw [heq] at hsteps_sig
    exact ElfImageRunsTo.of_exitsWith hload
      (processExitsWith_of_exited hsteps_sig hst)
      ⟨rfl, rfl, rfl, rfl⟩
  · have hsig : (toSigState sf).status = .Signaled sigAbrt := by
      simp [toSigState, hst, State.status_setStatus]
    exact ElfImageRunsTo.of_exitsWith hload
      (processExitsWith_of_signaled hsteps_sig hsig)
      ⟨rfl, rfl⟩

theorem cliRunsToWith_of_outcomeOf_observed {elf : ElfImage}
    {ext : String → Option (State → State)} {i : Inputs}
    {a : Cli.RunAnswer} {res : ProcessResult}
    (hout : outcomeOf elf (cliProgWith ext) (Cli.cliInputs i) = some res)
    (hobs : Cli.MainResult.Observed i.files (Cli.MainResult.ofAnswer a) res) :
    CliRunsToRawWith elf ext i (observe i.files a) := by
  rw [← Cli.MainResult.observed_ofAnswer i.files a res hobs]
  exact cliRunsToWith_of_outcomeOf hout

theorem cliRunsToWith_of_outcomeOf_usage {elf : ElfImage}
    {ext : String → Option (State → State)} {i : Inputs}
    {res : ProcessResult}
    (hout : outcomeOf elf (cliProgWith ext) (Cli.cliInputs i) = some res)
    (hobs : Cli.MainResult.Observed i.files (.ret 2 [] []) res) :
    CliRunsToRawWith elf ext i (.exited 2 [] (filesOf i.files)) := by
  rw [← Cli.MainResult.observed_usage i.files res hobs]
  exact cliRunsToWith_of_outcomeOf hout

theorem not_runAllocFails_of_trace_with {elf : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs}
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    ¬ Cli.RunAllocFails elf (cliProgWith ext) i := by
  rintro ⟨s0, sf, hload, hsteps, hmem⟩
  rw [cliInputs_eq_cliProcessInputs] at hload
  exact hno s0 (toSigState sf) hload
    (steps_cliProgWith_to_cliProgSigWith (loadState_status_running hload) hsteps)
    (by rwa [toSigState_trace])

/-- Unpatched allocation-failure witness on `cliProgAbortOnPanicUnderExterns ext` starting at `s0`. -/
def CliInputAllocFailsRawWith (elf : ElfImage) (ext : String → Option (State → State))
    (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgAbortOnPanicUnderExterns ext) s0 s ∧ RustHeap.allocFailedEvent ∈ s.trace

theorem cliInputAllocFails_eq_cliRunAllocFailsWith (elf : ElfImage) (W : CliHooks) (i : Inputs) :
    CliInputAllocFails elf W i = CliRunAllocFailsWith elf (cliHookExterns W) i := rfl

theorem cliInputAllocFailsRawWith_of_runAllocFails {elf : ElfImage}
    {ext : String → Option (State → State)} {i : Inputs}
    (h : Cli.RunAllocFails elf (cliProgWith ext) i) :
    CliInputAllocFailsRawWith elf ext i := by
  rcases h with ⟨s0, sf, hload, hsteps, hmem⟩
  rw [cliInputs_eq_cliProcessInputs] at hload
  have hsteps_sig := steps_cliProgWith_to_cliProgSigWith (loadState_status_running hload) hsteps
  exact ⟨s0, toSigState sf, hload, hsteps_sig, by rwa [toSigState_trace]⟩

theorem cliRunAllocFailsWith_of_raw {elf elf' : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hraw : CliInputAllocFailsRawWith elf' ext i) :
    CliRunAllocFailsWith elf ext i := by
  rcases hraw with ⟨s0', s, hload', hsteps, hmem⟩
  rw [hpatch] at hload'
  cases hload : elf.loadState (cliProcessInputs i) with
  | error _ =>
    rw [hload] at hload'
    cases hload'
  | ok s0 =>
    rw [hload] at hload'
    simp only [Except.map, Except.ok.injEq] at hload'
    subst hload'
    exact ⟨s0, s, hload, hsteps, hmem⟩

theorem cliRunsToWith_aborted_of_outcomeOf {elf : ElfImage} {ext : String → Option (State → State)}
    {i : Inputs}
    (hout : outcomeOf elf (cliProgWith ext) (Cli.cliInputs i) = some .aborted) :
    CliRunsToRawWith elf ext i .aborted :=
  cliRunsToWith_of_outcomeOf hout

theorem cliRunsToWith_of_main_stdinOverCap_symtabGhost {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i)
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    CliRunsToRawWith elf ext i (.exited 2 [] (filesOf i.files)) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main hE hH hG hmain hstk hstk' hi hl
    (Cli.MainCaseB2.stdinOverCap hstin)
  rw [cliProgWith_ofImage_eq himg hbase ext] at out
  rcases out with ⟨res, hout, hobs⟩ | halloc_fail
  · exact cliRunsToWith_of_outcomeOf_usage hout hobs
  · exact absurd halloc_fail (not_runAllocFails_of_trace_with hno)

theorem cliRunsToWith_of_main_sendOverCap_symtabGhost {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    CliRunsToRawWith elf ext i (observe i.files (some none)) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main hE hH hG hmain hstk hstk' hi hl
    (Cli.MainCaseB2.sendOverCap hover hnstin hcoins)
  rw [cliProgWith_ofImage_eq himg hbase ext] at out
  rcases out with ⟨res, hout, hobs⟩ | halloc_fail
  · exact cliRunsToWith_of_outcomeOf_observed (a := some none) hout hobs
  · exact absurd halloc_fail (not_runAllocFails_of_trace_with hno)

theorem cliRunsToWith_of_main_call_symtabGhost {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (hno : ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanicUnderExterns ext) s0 s → RustHeap.allocFailedEvent ∉ s.trace) :
    CliRunsToRawWith elf ext i (observe i.files a) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main hE hH hG hmain hstk hstk' hi hl
    (Cli.MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  rw [cliProgWith_ofImage_eq himg hbase ext] at out
  rcases out with ⟨res, hout, hobs⟩ | halloc_fail
  · exact cliRunsToWith_of_outcomeOf_observed hout hobs
  · exact absurd halloc_fail (not_runAllocFails_of_trace_with hno)

theorem cliRunsToWith_or_aborted_of_main_call_symtabGhost {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf)
    (hH : Cli.MuslHarness elf (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    CliRunsToRawWith elf ext i (observe i.files a) ∨
      (CliRunsToRawWith elf ext i .aborted ∧ CliInputAllocFailsRawWith elf ext i) := by
  obtain ⟨hstk, hstk'⟩ := Cli.MainHops.cli_stk_outcome
  have out := Cli.outcome_of_main_or_oom hE hH hG hmain hstk hstk' hi hl
    (Cli.MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  rw [cliProgWith_ofImage_eq himg hbase ext] at out
  rcases out with ⟨res, hout, hobs⟩ | ⟨habort, halloc_fail⟩
  · exact Or.inl (cliRunsToWith_of_outcomeOf_observed hout hobs)
  · exact Or.inr ⟨cliRunsToWith_aborted_of_outcomeOf habort,
      cliInputAllocFailsRawWith_of_runAllocFails halloc_fail⟩

theorem cliRunsToWith_or_aborted_of_main_call_patch_symtabGhost {elf elf' : ElfImage}
    {img : Obj.Image} {ext : String → Option (State → State)}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith ext)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
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
    CliRunsToUnderExterns elf ext i (observe i.files a) ∨
      (CliRunsToUnderExterns elf ext i .aborted ∧ CliRunAllocFailsWith elf ext i) := by
  rcases cliRunsToWith_or_aborted_of_main_call_symtabGhost himg hbase hE hH hG hmain
      hi hl hrun hnover hnstin hcoins hcommit with
    hraw | ⟨habort, hfail⟩
  · exact Or.inl (cliRunsToWith_of_raw hpatch hraw)
  · exact Or.inr ⟨cliRunsToWith_of_raw hpatch habort, cliRunAllocFailsWith_of_raw hpatch hfail⟩

/-- Guarded-extern single-call OOM-disjunction bridge from `Cli.mainSpecTight`, transferring `SymtabGhost`-guarded execution back to `ext`. -/
theorem cliRunsToWith_or_aborted_of_main_call_guard {elf elf' : ElfImage} {img : Obj.Image}
    {ext gExt : String → Option (State → State)}
    {A : RustHeap.RustAlloc} {Fr : SepProp} {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hG : SymtabGhost (Cli.cliProg img (cliExternsWith gExt)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExternsWith gExt)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hRunsTransfer : ∀ o, CliRunsToUnderExterns elf gExt i o → CliRunsToUnderExterns elf ext i o)
    (hAllocTransfer : CliRunAllocFailsWith elf gExt i → CliRunAllocFailsWith elf ext i)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    CliRunsToUnderExterns elf ext i (observe i.files a) ∨
      (CliRunsToUnderExterns elf ext i .aborted ∧ CliRunAllocFailsWith elf ext i) := by
  rcases cliRunsToWith_or_aborted_of_main_call_patch_symtabGhost himg hbase hE hH hG hmain hpatch
      hi hl hrun hnover hnstin hcoins hcommit with
    hok | ⟨habort, hfail⟩
  · exact Or.inl (hRunsTransfer _ hok)
  · exact Or.inr ⟨hRunsTransfer _ habort, hAllocTransfer hfail⟩

/-- Parameterized `CliBinaryCorrectExt elf` composer over an extern-guard operator `gfn` supplying `SymtabGhost` and run/allocation transfer. -/
theorem cliBinaryCorrectExt_of_parts_observe_guard {elf elf' : ElfImage} {img : Obj.Image}
    (gfn : (String → Option (State → State)) → String → Option (State → State))
    (hGuardOk : ∀ P A ext, CliExternsOk P A ext → CliExternsOk P A (gfn ext))
    (hGuardSymtab : ∀ ext, SymtabGhost (Cli.cliProg img (cliExternsWith (gfn ext))))
    (hGuardRuns : ∀ ext i o, CliRunsToUnderExterns elf (gfn ext) i o → CliRunsToUnderExterns elf ext i o)
    (hGuardAlloc : ∀ C ext, CliAllocNeverFailsWith elf C ext →
      CliAllocNeverFailsWith elf C (gfn ext))
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      ∃ Fr : SepProp,
        Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
          (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
          (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      ∃ Run : Inputs → Cli.RunAnswer → Prop,
        subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
          (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
        (∀ g m, Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
          ∃ a, Run (smSendInputs g m) a ∧
            observe (smSendInputs g m).files a =
              observe (smSendInputs g m).files (smSendModel P.C g m) ∧
            Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
        (∀ g c rc, Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
          ∃ a, Run (smRecvInputs g c rc) a ∧
            observe (smRecvInputs g c rc).files a =
              observe (smRecvInputs g c rc).files (smRecvModel P.C g c rc) ∧
            Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))) :
    CliBinaryCorrectExt elf := by
  refine ⟨hcode, fun P A ext hOk halloc => ?_⟩
  let gExt := gfn ext
  have hOk' : CliExternsOk P A gExt := hGuardOk P A ext hOk
  have halloc_g : CliAllocNeverFailsWith elf P.C gExt := hGuardAlloc P.C ext halloc
  have halloc' := cliAllocNeverFailsRawWith_of_patch hpatch halloc_g
  obtain ⟨Fr, hH'⟩ := hH P A gExt hOk'
  obtain ⟨Run, hmain', hsend, hrecv⟩ := hmain P A gExt hOk'
  have hG' : SymtabGhost (Cli.cliProg img (cliExternsWith gExt)) := hGuardSymtab ext
  refine ⟨fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact hGuardRuns ext _ _ (cliRunsToWith_of_raw (hpatch (smSendInputs g m))
        (cliRunsToWith_of_main_stdinOverCap_symtabGhost himg hbase hE hH' hG' hmain'
          (cliInputsOk_smSendInputs g m)
          (inputsLoadable_smInputs g _ _ _ hg (by decide))
          (isStdinOverCap_smSendInputs g m hstin)
          (halloc'.1 g m hg hm)))
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ Cli.IsStdinOverCap (smSendInputs g m) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact hGuardRuns ext _ _ (cliRunsToWith_of_raw (hpatch (smSendInputs g m))
          (cliRunsToWith_of_main_sendOverCap_symtabGhost himg hbase hE hH' hG' hmain'
            (cliInputsOk_smSendInputs g m)
            (inputsLoadable_smInputs g _ _ _ hg (by decide))
            (isSendOverCap_smSendInputs g m (by unfold maxPlaintextBytes at hover; exact hover))
            hnstin
            (Cli.coinsReadable_smInputs g (.send (partyAddress g.party.other)) [] m (by decide))
            (halloc'.1 g m hg hm)))
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hsend g m hg hm
        rw [← hobs]
        exact hGuardRuns ext _ _ (cliRunsToWith_of_raw (hpatch (smSendInputs g m))
          (cliRunsToWith_of_main_call_symtabGhost himg hbase hE hH' hG' hmain'
            (cliInputsOk_smSendInputs g m)
            (inputsLoadable_smInputs g _ _ _ hg (by decide))
            hrun
            (not_isSendOverCap_of_stdin_le (by simp only [smSendInputs, smInputs]; unfold maxPlaintextBytes at hover; omega))
            hnstin
            (Cli.coinsReadable_smInputs g (.send (partyAddress g.party.other)) [] m (by decide))
            hcommit
            (halloc'.1 g m hg hm)))
  · by_cases hstin : (msgTypeWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact hGuardRuns ext _ _ (cliRunsToWith_of_raw (hpatch (smRecvInputs g c rc))
        (cliRunsToWith_of_main_stdinOverCap_symtabGhost himg hbase hE hH' hG' hmain'
          (cliInputsOk_smRecvInputs g c rc)
          (inputsLoadable_smInputs g _ _ _ hg (by simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]))
          (isStdinOverCap_smRecvInputs g c rc hstin)
          (halloc'.2 g c rc hg hc)))
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hrecv g c rc hg hc
      rw [← hobs]
      exact hGuardRuns ext _ _ (cliRunsToWith_of_raw (hpatch (smRecvInputs g c rc))
        (cliRunsToWith_of_main_call_symtabGhost himg hbase hE hH' hG' hmain'
          (cliInputsOk_smRecvInputs g c rc)
          (inputsLoadable_smInputs g _ _ _ hg (by simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]))
          hrun
          (not_isSendOverCap_smRecvInputs g c rc)
          (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
          (Cli.coinsReadable_smInputs g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc)
            (msgTypeWhisper :: c) (by simp [HMAC.keyToBytes32, fileCapBytes]))
          hcommit
          (halloc'.2 g c rc hg hc)))

theorem cliBinaryCorrectExt_of_parts_guard {elf elf' : ElfImage} {img : Obj.Image}
    (gfn : (String → Option (State → State)) → String → Option (State → State))
    (hGuardOk : ∀ P A ext, CliExternsOk P A ext → CliExternsOk P A (gfn ext))
    (hGuardSymtab : ∀ ext, SymtabGhost (Cli.cliProg img (cliExternsWith (gfn ext))))
    (hGuardRuns : ∀ ext i o, CliRunsToUnderExterns elf (gfn ext) i o → CliRunsToUnderExterns elf ext i o)
    (hGuardAlloc : ∀ C ext, CliAllocNeverFailsWith elf C ext →
      CliAllocNeverFailsWith elf C (gfn ext))
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      ∃ Fr : SepProp,
        Cli.MuslHarness elf' (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName) Fr
          (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
          (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : ∀ (P : PEParams) (A : RustHeap.RustAlloc) (ext : String → Option (State → State)),
      CliExternsOk P A ext →
      ∃ Run : Inputs → Cli.RunAnswer → Prop,
        subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img Cli.mainName)
          (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
        (∀ g m, Reach (spqrOffSessionParams P.C) g → m.length < 2 ^ 32 →
          Run (smSendInputs g m) (smSendModel P.C g m)) ∧
        (∀ g c rc, Reach (spqrOffSessionParams P.C) g → c.length < 2 ^ 32 →
          Run (smRecvInputs g c rc) (smRecvModel P.C g c rc))) :
    CliBinaryCorrectExt elf := by
  refine cliBinaryCorrectExt_of_parts_observe_guard gfn hGuardOk hGuardSymtab hGuardRuns
    hGuardAlloc himg hbase hcode hpatch hE hH (fun P A ext hOk => ?_)
  obtain ⟨Run, hmain', hsend, hrecv⟩ := hmain P A ext hOk
  exact ⟨Run, hmain',
    fun g m hg hm => ⟨_, hsend g m hg hm, rfl, commitOk_smSendModel P.C g m⟩,
    fun g c rc hg hc => ⟨_, hrecv g c rc hg hc, rfl, commitOk_smRecvModel P.C g c rc⟩⟩

end ProcessBridge

end CryptoVerification.SignalSession
