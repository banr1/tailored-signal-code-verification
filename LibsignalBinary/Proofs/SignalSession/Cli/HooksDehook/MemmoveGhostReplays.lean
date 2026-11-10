/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Stock-Safe `StepsVisitedIn` Witnesses & `GhostExternReplaysOn` / `S` Bridges (`HooksDehook.MemmoveGhostReplays`)

Companion replay module for Card **L3-b** (`MemmoveGhost{,K}`), split cleanly under 1,200 lines:

1. **Stock-safe `h2fsgen_StepsVisitedIn` first-stop witnesses (§1):**
   `memmoveGhostFn{,K}_visitedIn`, `f3EmptyMemmoveGhostHook{,K}_visitedIn`, and
   `f3PureMemmoveGhostHook{,K}_visitedIn` via
   `ElfSlicesPqOomH2FirstStopGeneric.h2fsgen_real_subroutine_run_visitedIn_of_stripS` +
   `h2fsgen_stepsUntil_det` (`0` `h2sl_stepsUntil_emptyProg_to_realW`, `0` `h2fsgen_HooksUnfetched`,
   `0` `StepsUntil`-style `hLift`).
2. **Memory-guarded `P_run → P_real` per-stub replays via `hLiftVis` (§2, **H1**):**
   `memmoveGhostFn{,K}_replayOn_of_visitedIn`, `f3EmptyMemmoveGhostHook{,K}_replayOn_of_visitedIn`,
   and `f3PureMemmoveGhostHook{,K}_replayOn_of_visitedIn` evaluate `hInvLoaded` strictly at the
   call-site memory `u.mem` and transport `InvMem` to `(f u).mem` via `hInvKf` +
   `hSteps.keepsFrozen`, never at `s0.mem` (**H1**).
3. **Single-stub `GhostExternReplaysS` & `GhostExternReplaysOn` packagers (§3):**
   Trajectory-independent `S` and trajectory-aware `On` packagers at outer `keepR` (plain) and
   polymorphic `keep_any` (`K`).
4. **C11 `keep_any` (`keep_outer := fun _ => false`) trajectory replay bridges & 3-entry `C4`/`F1`
   premise packagers (§4):**
   `f3EmptyMemmoveGhostHook_replayAtStub_of_lrOut`, `f3EmptyMemmoveGhostHook_replaysOn_of_lrOut`,
   and `f3PureMemmoveGhostHook_{replayAtStub,replaysOn}_of_lrOut` discharge C11's `GhostRowReplayOn`
   from trajectory-level `hlr_stub`; `rowSyms_reg_ext_of_entries` and `bPreHull3_reg_ext_of_entries`
   package the **verbatim 3-entry premise shapes** of `Lib2LayoutFacts.lean:392-402` / `:346-353` /
   `:355-362` @ `a230f2671b` (`origin/stock-lld/c2-startup-dnm`, NOT imported; cf.
   `keepTextBPre_sub_rxProg` `:114`, `f3CodeInv_rxWords_codeLoaded_strip` `:203`,
   `C2ExternTableFacts` `:316`, `f3Row_ghostProg617_externAt_none_of_ne_entry` `:368`,
   `StepsVisitedIn` `:428`, `f3RxSeg_steps_realW_of_visitedIn` `:444`) over
   `["memmove", "memcpy", "memset"]` for `L3-d` (`MemmoveLrTrap`) and card `c`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_single_stub ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_real_subroutine_run_visitedIn_of_stripS h2fsgen_stepsUntil_det
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (
  masterMemmoveSpec memmoveSpecK
  masterMemmoveSpec_stripSInvariant masterMemmoveSpecK_stripSInvariant
  masterMemmoveSpec_preservesFsTrace masterMemmoveSpecK_preservesFsTrace
  masterMemmoveSpec_pre_setPC masterMemmoveSpecK_pre_setPC
  masterMemmoveSpec_outcome_setPC masterMemmoveSpecK_outcome_setPC
  bPrePadWord bPreMemmoveByteOff bPreHullWords
  pureWordsProg_bPreHull_hasWords
  subroutine_ok_bPreHull_masterMemmove_of_hasWords
  subroutine_ok_bPreHull_masterMemmoveK_of_hasWords
  TrapRetHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (
  keepBPreHull memmoveGhostFn memmoveGhostFnK
  memmoveGhostFnK_keepLr_false_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK (
  f3EmptyMemmoveGhostHook f3EmptyMemmoveGhostHookK
  f3PureMemmoveGhostHook f3PureMemmoveGhostHookK
  f3EmptyMemmoveGhostHook_eq f3EmptyMemmoveGhostHookK_eq
)

/-! ## 1. Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Execution Witnesses -/

private theorem linkedCallHook_eq_choose_of_active {α : Type}
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {entry : BitVec 64}
    {spec : Spec α} {fallback : State → State} {u : State}
    (hActPre : ActiveRealPre spec u)
    (hReal : ActiveRealRun keepR P_run P_sub entry u) :
    linkedCallHook keepR P_run P_sub entry spec fallback u = Classical.choose hReal.2.2.2 := by
  classical
  unfold linkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop execution witness for
    `memmoveGhostFn` (`0` `emptyLift`, `0` `HooksUnfetched`), pinning the `Classical.choose`
    endpoint via `h2fsgen_stepsUntil_det`. -/
theorem memmoveGhostFn_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC (m + bPreMemmoveByteOff))
        (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u) ∧
      SubroutineStop u (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + bPreMemmoveByteOff))
        (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u) := by
  classical
  have hActPre : ActiveRealPre masterMemmoveSpec u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_bPreHull_masterMemmove_of_hasWords hsub_no hhull hres)
      (masterMemmoveSpec_stripSInvariant keepR)
      masterMemmoveSpec_preservesFsTrace
      masterMemmoveSpec_pre_setPC
      masterMemmoveSpec_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub (m + bPreMemmoveByteOff) u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u =
      Classical.choose hReal.2.2.2 :=
    linkedCallHook_eq_choose_of_active hActPre hReal
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop execution witness for
    `memmoveGhostFnK`, deriving `keepR (u.readReg64 .lr) = false` automatically from `hnoex`. -/
theorem memmoveGhostFnK_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC (m + bPreMemmoveByteOff))
        (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u) ∧
      SubroutineStop u (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + bPreMemmoveByteOff))
        (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u) := by
  classical
  have hlr_out : keepR (u.readReg64 .lr) = false :=
    memmoveGhostFnK_keepLr_false_of_noException hnoex
  have hActPre : ActiveRealPre (memmoveSpecK keepR masterMemmoveSpec) u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_bPreHull_masterMemmoveK_of_hasWords keepR hsub_no hhull hres)
      (masterMemmoveSpecK_stripSInvariant keepR keepR)
      (masterMemmoveSpecK_preservesFsTrace keepR)
      (masterMemmoveSpecK_pre_setPC keepR)
      (masterMemmoveSpecK_outcome_setPC keepR)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub (m + bPreMemmoveByteOff) u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u =
      Classical.choose hReal.2.2.2 :=
    linkedCallHook_eq_choose_of_active hActPre hReal
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` first-stop witness for
    `f3EmptyMemmoveGhostHook` (feeds C2's `f3RxSeg_steps_realW_of_visitedIn` in card `c`). -/
theorem f3EmptyMemmoveGhostHook_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (m + bPreMemmoveByteOff))
        (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      SubroutineStop u (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff))
        (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) := by
  rw [f3EmptyMemmoveGhostHook_eq] at hnoex ⊢
  exact memmoveGhostFn_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres
    hrun hnoex hFr hlr_out hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` first-stop witness for
    `f3EmptyMemmoveGhostHookK` (zero caller `lr` premise). -/
theorem f3EmptyMemmoveGhostHookK_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (m + bPreMemmoveByteOff))
        (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      SubroutineStop u (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff))
        (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u) := by
  rw [f3EmptyMemmoveGhostHookK_eq] at hnoex ⊢
  exact memmoveGhostFnK_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres
    hrun hnoex hFr hCodeSub

theorem f3PureMemmoveGhostHook_visitedIn
    {keepR : BitVec 64 → Bool} {m : BitVec 64}
    {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3PureMemmoveGhostHook keepR m resolve padWord u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded
      (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (m + bPreMemmoveByteOff))
        (f3PureMemmoveGhostHook keepR m resolve padWord u) ∧
      SubroutineStop u (f3PureMemmoveGhostHook keepR m resolve padWord u) ∧
      ExecFrozen (f3PureMemmoveGhostHook keepR m resolve padWord u).mem ∧
      (f3PureMemmoveGhostHook keepR m resolve padWord u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff))
        (f3PureMemmoveGhostHook keepR m resolve padWord u) :=
  f3EmptyMemmoveGhostHook_visitedIn rfl
    (pureWordsProg_externAt_none m (bPreHullWords m resolve padWord))
    (pureWordsProg_bPreHull_hasWords m resolve padWord) hres hrun hnoex hFr hlr_out hCodeSub

theorem f3PureMemmoveGhostHookK_visitedIn
    {keepR : BitVec 64 → Bool} {m : BitVec 64}
    {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3PureMemmoveGhostHookK keepR m resolve padWord u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded
      (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC (m + bPreMemmoveByteOff))
        (f3PureMemmoveGhostHookK keepR m resolve padWord u) ∧
      SubroutineStop u (f3PureMemmoveGhostHookK keepR m resolve padWord u) ∧
      ExecFrozen (f3PureMemmoveGhostHookK keepR m resolve padWord u).mem ∧
      (f3PureMemmoveGhostHookK keepR m resolve padWord u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff))
        (f3PureMemmoveGhostHookK keepR m resolve padWord u) :=
  f3EmptyMemmoveGhostHookK_visitedIn rfl
    (pureWordsProg_externAt_none m (bPreHullWords m resolve padWord))
    (pureWordsProg_bPreHull_hasWords m resolve padWord) hres hrun hnoex hFr hCodeSub

/-! ## 2. Memory-Guarded `P_run → P_real` Per-Stub Replays via `hLiftVis` (H1: `u.mem` / `(f u).mem`) -/

/-- Memory-guarded `P_run → P_real` per-stub replay for `memmoveGhostFn` via `hLiftVis`.
    **H1:** `hInvLoaded` is evaluated strictly at `u.mem` (`hInvLoaded u.mem hfr hinv`) and
    transported to `(f u).mem` via `hInvKf u.mem _ hinv hSteps.keepsFrozen` (never at `s0.mem`). -/
theorem memmoveGhostFn_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepR (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).mem ∧
      InvMem (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨_, _, hfr_sf, hfs_sf, hvis⟩ :=
    memmoveGhostFn_visitedIn hsvc_run hsvc_sub hrun_no hsub_no hhull hres
      hrun hnoex hfr hlr (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC (m + bPreMemmoveByteOff)) :=
    hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC (m + bPreMemmoveByteOff))
      (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u) :=
    hLiftVis u _ hrun hfr hinv hvis
  have hSteps : Steps P_real u (memmoveGhostFn keepR P_run P_sub (m + bPreMemmoveByteOff) u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Memory-guarded `P_run → P_real` per-stub replay for `memmoveGhostFnK` via `hLiftVis` (zero
    caller `lr` premise; **H1:** `hInvLoaded` at `u.mem`, transported to `(f u).mem`). -/
theorem memmoveGhostFnK_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).mem ∧
      InvMem (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨_, _, hfr_sf, hfs_sf, hvis⟩ :=
    memmoveGhostFnK_visitedIn hsvc_run hsvc_sub hrun_no hsub_no hhull hres
      hrun hnoex hfr (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC (m + bPreMemmoveByteOff)) :=
    hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC (m + bPreMemmoveByteOff))
      (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u) :=
    hLiftVis u _ hrun hfr hinv hvis
  have hSteps : Steps P_real u (memmoveGhostFnK keepR P_run P_sub (m + bPreMemmoveByteOff) u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Memory-guarded `emptyStdProg → P_real` per-stub replay for `f3EmptyMemmoveGhostHook` via the
    stock-safe `hLiftVis` premise (left as a premise for card `c` to discharge via C2's
    `f3RxSeg_steps_realW_of_visitedIn`; **H1:** `hInvLoaded` at `u.mem`). -/
theorem f3EmptyMemmoveGhostHook_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepR (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      InvMem (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).fs = u.fs := by
  simp only [f3EmptyMemmoveGhostHook_eq]
  exact memmoveGhostFn_replayOn_of_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres
    hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- Memory-guarded `emptyStdProg → P_real` per-stub replay for `f3EmptyMemmoveGhostHookK` via
    `hLiftVis` (zero caller `lr` premise; **H1:** `hInvLoaded` at `u.mem`). -/
theorem f3EmptyMemmoveGhostHookK_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      InvMem (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).fs = u.fs := by
  simp only [f3EmptyMemmoveGhostHookK_eq]
  exact memmoveGhostFnK_replayOn_of_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hhull hres
    hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

theorem f3PureMemmoveGhostHook_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3PureMemmoveGhostHook keepR m resolve padWord u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepR (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (f3PureMemmoveGhostHook keepR m resolve padWord u) ∧
      ExecFrozen (f3PureMemmoveGhostHook keepR m resolve padWord u).mem ∧
      InvMem (f3PureMemmoveGhostHook keepR m resolve padWord u).mem ∧
      (f3PureMemmoveGhostHook keepR m resolve padWord u).fs = u.fs :=
  f3EmptyMemmoveGhostHook_replayOn_of_visitedIn rfl
    (pureWordsProg_externAt_none m (bPreHullWords m resolve padWord))
    (pureWordsProg_bPreHull_hasWords m resolve padWord)
    hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

theorem f3PureMemmoveGhostHookK_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3PureMemmoveGhostHookK keepR m resolve padWord u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f3PureMemmoveGhostHookK keepR m resolve padWord u) ∧
      ExecFrozen (f3PureMemmoveGhostHookK keepR m resolve padWord u).mem ∧
      InvMem (f3PureMemmoveGhostHookK keepR m resolve padWord u).mem ∧
      (f3PureMemmoveGhostHookK keepR m resolve padWord u).fs = u.fs :=
  f3EmptyMemmoveGhostHookK_replayOn_of_visitedIn rfl
    (pureWordsProg_externAt_none m (bPreHullWords m resolve padWord))
    (pureWordsProg_bPreHull_hasWords m resolve padWord)
    hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-! ## 3. Single-Stub `GhostExternReplaysS` & `GhostExternReplaysOn` Packagers -/

theorem f3EmptyMemmoveGhostHook_replaysS_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    GhostExternReplaysS keepR (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemmoveGhostHook_replayOn_of_visitedIn
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

theorem f3EmptyMemmoveGhostHookK_replaysS_of_visitedIn
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemmoveGhostHookK_replayOn_of_visitedIn
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

theorem f3EmptyMemmoveGhostHook_replaysOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf') :
    GhostExternReplaysOn keepR (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := f3EmptyMemmoveGhostHook_replayOn_of_visitedIn
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ _ hpc hrun hnoex _ hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

theorem f3EmptyMemmoveGhostHookK_replaysOn_of_visitedIn
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf') :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := f3EmptyMemmoveGhostHookK_replayOn_of_visitedIn
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ _ hpc hrun hnoex _ hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-! ## 4. C11 `keep_any` (`keep_outer := fun _ => false`) Trajectory Replays & Verbatim 3-Entry `C4`/`F1` Packagers -/

/-- Trajectory-level per-stub replay for plain `f3EmptyMemmoveGhostHook` polymorphic in `keep_any`
    (specifically `keep_any := fun _ => false` for C11 `ExtraGhostReplay.GhostRowReplayOn` Arm 2),
    discharging `keepR (u.readReg64 .lr) = false` via `hlr_stub` along `Steps P_ghost s0 u` +
    `Steps P_ghost (f u) sf` (closed in `L3-d` `MemmoveLrTrap`). -/
theorem f3EmptyMemmoveGhostHook_replayAtStub_of_lrOut
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf')
    (hlr_stub : ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      keepR (u.readReg64 .lr) = false) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem →
      ExecFrozen u.mem →
      keep_any (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) ∧
      ExecFrozen (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem ∧
      InvMem (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem := by
  have hRep := f3EmptyMemmoveGhostHook_replayOn_of_visitedIn
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  refine ⟨hRep.1, fun u hpre hpost hpc hrun hnoex _ hfr _ hinv => ?_⟩
  have hlr : keepR (u.readReg64 .lr) = false :=
    hlr_stub u hpre hpost hpc hrun hnoex hfr hinv
  obtain ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv'⟩

/-- Single-stub `GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf`
    for plain `f3EmptyMemmoveGhostHook` (polymorphic in `keep_any`, e.g. `fun _ => false` in C11)
    from trajectory-level `hlr_stub`. -/
theorem f3EmptyMemmoveGhostHook_replaysOn_of_lrOut
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf')
    (hlr_stub : ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      keepR (u.readReg64 .lr) = false) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf :=
  ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    (f3EmptyMemmoveGhostHook_replayAtStub_of_lrOut keep_any
      hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis hlr_stub)

theorem f3PureMemmoveGhostHook_replaysOn_of_lrOut
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real : Program}
    {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64} (padWord : BitVec 32 := bPrePadWord)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3PureMemmoveGhostHook keepR m resolve padWord))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf')
    (hlr_stub : ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3PureMemmoveGhostHook keepR m resolve padWord u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3PureMemmoveGhostHook keepR m resolve padWord u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      keepR (u.readReg64 .lr) = false) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf :=
  f3EmptyMemmoveGhostHook_replaysOn_of_lrOut keep_any hghost_stub hother hreal_fr rfl
    (pureWordsProg_externAt_none m (bPreHullWords m resolve padWord))
    (pureWordsProg_bPreHull_hasWords m resolve padWord)
    hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis hlr_stub

/-- Multi-entry `hreg_ext` packager (**C4 + F1**, zero off-train C2 imports) whose premises copy
    verbatim the binder and proposition shapes of
    `LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfF3Relink/Lib2LayoutFacts.lean` @ `a230f2671b`
    (`origin/stock-lld/c2-startup-dnm`, NOT imported; cf. `C2ExternTableFacts` `:316`,
    `f3Row_ghostProg617_externAt_none_of_ne_entry` `:368`):
    - `hOffEntries`: verbatim conclusion shape of
      `Lib2LayoutFacts.lean:392-402` `f3RowSyms_ghostProg617_externAt_none_of_ne_entries`
      (backed by `:346-353` `f3RxSeg_ghostProg617_externAt_none_of_ne_entries`), discharged by
      `exact` at C2 assembly;
    - `hEntry`: verbatim lookup shape of
      `Lib2LayoutFacts.lean:355-362` `f3RxSeg_ghostProg617_externAt_entry`. -/
theorem rowSyms_reg_ext_of_entries
    {keepR_row : BitVec 64 → Bool} {P_ghost : Program}
    {rowSyms : List String} {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hOffEntries : ∀ {pc : BitVec 64},
      keepR_row pc = true → pc ∉ rowSyms.map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String},
      sym ∈ rowSyms → P_ghost.externAt? (resolve sym) = extOf sym)
    (hTraps : ∀ {sym : String} {f : State → State},
      sym ∈ rowSyms → extOf sym = some f → ∀ L, keepR_row L = true → TrapRetHook L f) :
    ∀ L : BitVec 64, keepR_row L = true →
      ∀ pc : BitVec 64, keepR_row pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapRetHook L f := by
  intro L hL pc hpc
  by_cases hmem : pc ∈ rowSyms.map resolve
  · obtain ⟨sym, hsym, rfl⟩ := List.mem_map.mp hmem
    rw [hEntry hsym]
    cases hext : extOf sym with
    | none => exact Or.inl rfl
    | some f => exact Or.inr ⟨f, rfl, hTraps hsym hext L hL⟩
  · exact Or.inl (hOffEntries hpc hmem)

/-- Concrete 3-symbol specialization of `rowSyms_reg_ext_of_entries` to `.text.b_pre`'s
    `keepBPreHull m` and `rowSyms := ["memmove", "memcpy", "memset"]` (**C4 + F1**, citing
    `Lib2LayoutFacts.lean:392-402, :346-353, :355-362` @ `a230f2671b`, NOT imported):
    - `"memmove"` requires `TrapRetHook L f` only for `keepBPreHull m L = true`
      (`MemmoveGhostK.trapRetHook_f3EmptyMemmoveGhostHook{,K}`);
    - `"memcpy"` and `"memset"` accept universal `∀ L, TrapRetHook L f`
      (`MemmoveCode.trapRetHook_linkedCallHook_of_hookOk_and_lr` `:1155`), covering Stage A's
      narrow `keepMemcpyBlk20` / `keepMemsetBlk21` where `keep L = false` on `[m + 660, m + 956)`. -/
theorem bPreHull3_reg_ext_of_entries
    {m : BitVec 64} {P_ghost : Program}
    {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hOffEntries : ∀ {pc : BitVec 64},
      keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve →
      P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveTrap : ∀ f, extOf "memmove" = some f →
      ∀ L, keepBPreHull m L = true → TrapRetHook L f)
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapRetHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapRetHook L f) :
    ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapRetHook L f := by
  refine rowSyms_reg_ext_of_entries hOffEntries hEntry ?_
  intro sym f hsym hext L hL
  rcases List.mem_cons.mp hsym with rfl | h1
  · exact hMemmoveTrap f hext L hL
  · rcases List.mem_cons.mp h1 with rfl | h2
    · exact hMemcpyTrap f hext L
    · rcases List.mem_cons.mp h2 with rfl | hnil
      · exact hMemsetTrap f hext L
      · cases hnil

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays
