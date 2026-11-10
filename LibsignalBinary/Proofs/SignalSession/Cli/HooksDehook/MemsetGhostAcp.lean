/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness -- proof-setup: allow-public-import
import ProofLib.Process.OracleEq

/-!
# Pointwise `sigActions ∧ oracle` Preservation for `memset` Ghost Hooks (`HooksDehook.MemsetGhostAcp`)

Supplies the remaining two `AllocCallPreserved` conjuncts (`sigActions` and `oracle`) pointwise
for `memsetGhostHook`, `memsetGhostHookK`, `f3EmptyMemsetGhostHook`, `f3EmptyMemsetGhostHookK`,
`narrowMemsetGhostHook`, and `f3EmptyMemsetGhostHookNarrow` without touching `MemsetGhost`,
`MemsetGhostK`, `NarrowMemOpsR1`, or `NarrowF3R1Witness` (`0` upstream `.olean` invalidations and
`0` `Elf*` imports).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostAcp

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open ProofLib.StdStartup (StdStatePreserved stdMemsetSpec)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealRun linkedCallHook satisfies_stripExecOutside stepsUntil_of_stripS_standard
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords
  masterMemsetSpec memsetSpecK
  stdMemset_pre_of_masterMemset_pre subroutine_ok_stdMemset_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  keepFsTrace_hookMemset_eq keepMemsetBlk21 memsetGhostHook memsetGhostHookK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  f3EmptyMemsetGhostHook f3EmptyMemsetGhostHookK
  f3EmptyMemsetGhostHook_eq f3EmptyMemsetGhostHookK_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowMemOpsR1 (
  narrowMemsetGhostHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness (
  f3EmptyMemsetGhostHookNarrow f3EmptyMemsetGhostHookNarrow_eq_narrow
)

private theorem subroutineStop_of_stdMemsetOutcome
    {x : BitVec 64 × BitVec 8 × Nat} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome stdMemsetSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · dsimp only [stdMemsetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [stdMemsetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [stdMemsetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

private theorem activeRealRun_sigActions_and_oracle
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    {x : BitVec 64 × BitVec 8 × Nat} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterMemsetSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keep P_real P_sub entryTarget s0) :
    (Classical.choose hReal.2.2.2).sigActions = s0.sigActions ∧
      (Classical.choose hReal.2.2.2).oracle = s0.oracle := by
  have hpre : s0.mem ⊨ stdMemsetSpec.pre x s0 ∗ R := stdMemset_pre_of_masterMemset_pre hpreM
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ stdMemsetSpec.pre x s1 ∗ R := by
    rcases x with ⟨_, _, _⟩; cases s0; exact hpre
  have hs1'_pre : s1'.mem ⊨ stdMemsetSpec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : stdMemsetSpec.pre x s1' = stdMemsetSpec.pre x s1 := by
      dsimp only [s1']
      rcases x with ⟨_, _, _⟩; cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome (subroutine_ok_stdMemset_of_hasWords hsub_no hwords)
      x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_stdMemsetOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, _hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  have horc' : sf'.oracle = s1'.oracle := Steps.oracle_eq_of_standard hsvc_sub hsub_no hsteps'
  rw [hsf_eq] at horc'
  have horc : sf.oracle = s0.oracle := by
    dsimp only [s1', s1] at horc'
    cases s0; cases sf; exact horc'
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [stdMemsetSpec] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : StdStatePreserved s1' sf' := hpost'.1.2
    rw [hsf_eq] at hstd'
    refine ⟨?_, horc⟩
    dsimp only [s1', s1] at hstd'
    cases s0; cases sf; exact hstd'.2.2.2.1
  · dsimp only [stdMemsetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [stdMemsetSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [stdMemsetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Pointwise `sigActions ∧ oracle` preservation for `memsetGhostHook`. -/
theorem memsetGhostHook_acp
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (memsetGhostHook keep P_real P_sub entryTarget s0).sigActions = s0.sigActions ∧
      (memsetGhostHook keep P_real P_sub entryTarget s0).oracle = s0.oracle := by
  classical
  unfold memsetGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact activeRealRun_sigActions_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre hReal
    · rw [keepFsTrace_hookMemset_eq]
      cases s0; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Pointwise `sigActions ∧ oracle` preservation for `memsetGhostHookK`. -/
theorem memsetGhostHookK_acp
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (memsetGhostHookK keep P_real P_sub entryTarget s0).sigActions = s0.sigActions ∧
      (memsetGhostHookK keep P_real P_sub entryTarget s0).oracle = s0.oracle := by
  classical
  unfold memsetGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact activeRealRun_sigActions_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre.2 hReal
    · rw [keepFsTrace_hookMemset_eq]
      cases s0; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Pointwise `sigActions ∧ oracle` preservation for `f3EmptyMemsetGhostHook`. -/
theorem f3EmptyMemsetGhostHook_acp
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (f3EmptyMemsetGhostHook keep P_sub entryTarget s0).sigActions = s0.sigActions ∧
      (f3EmptyMemsetGhostHook keep P_sub entryTarget s0).oracle = s0.oracle := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact memsetGhostHook_acp rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

/-- Pointwise `sigActions ∧ oracle` preservation for `f3EmptyMemsetGhostHookK`. -/
theorem f3EmptyMemsetGhostHookK_acp
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0).sigActions = s0.sigActions ∧
      (f3EmptyMemsetGhostHookK keep P_sub entryTarget s0).oracle = s0.oracle := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact memsetGhostHookK_acp rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords s0

private theorem mallocngBlockProg21_svc_eq (mmpl : MultiPlacement) :
    (mallocngBlockProg mmpl 21 Syscall.standard).svc = Syscall.standard := rfl

private theorem stdProg_externAt_none (pc : BitVec 64) :
    (Program.ofSvc Syscall.standard).externAt? pc = none := rfl

/-- Pointwise `sigActions ∧ oracle` preservation for `narrowMemsetGhostHook`. -/
theorem narrowMemsetGhostHook_acp (mmpl : MultiPlacement) (s : State) :
    (narrowMemsetGhostHook mmpl s).sigActions = s.sigActions ∧
      (narrowMemsetGhostHook mmpl s).oracle = s.oracle :=
  memsetGhostHook_acp rfl (mallocngBlockProg21_svc_eq mmpl)
    (fun pc _ => stdProg_externAt_none pc)
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) s

/-- Pointwise `sigActions ∧ oracle` preservation for `f3EmptyMemsetGhostHookNarrow`
    (`rfl`-equal to `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow`). -/
theorem f3EmptyMemsetGhostHookNarrow_acp (mmpl : MultiPlacement) (s : State) :
    (f3EmptyMemsetGhostHookNarrow mmpl s).sigActions = s.sigActions ∧
      (f3EmptyMemsetGhostHookNarrow mmpl s).oracle = s.oracle := by
  rw [f3EmptyMemsetGhostHookNarrow_eq_narrow]
  exact narrowMemsetGhostHook_acp mmpl s

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostAcp
