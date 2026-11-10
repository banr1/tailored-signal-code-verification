/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK -- proof-setup: allow-public-import

/-!
# `GhostExternReplaysOn` / `GhostExternReplaysS` & `StepsVisitedIn` Bridges for `memrchr` (`HooksDehook.MemrchrGhostReplaysOn`)

Card **R2-b** replay module for `memrchr` (mirroring `HooksDehook.BcmpGhostK` §4–§5 and
`HooksDehook.MemcpyGhostReplaysOn`):

1. **Direct `P_real` Guarded Replay (`memrchrGhostFn{Ls,,K}_replayOn`):**
   - Route `β′` (`memrchrGhostFnLs`) discharges `keepR (u.readReg64 .lr) = false` automatically from
     `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false` (`K3`) + `hnoex`.
   - `K`-narrowed (`memrchrGhostFnK`) discharges `keepR (u.readReg64 .lr) = false` unconditionally
     from `hnoex`.
   - Raw plain (`memrchrGhostFn`) takes `keepR (u.readReg64 .lr) = false` at call sites.
2. **Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witnesses & `GhostExternReplays{On,S}`:**
   Provides `*_visitedIn`, `*_replayOn_of_visitedIn`, `*_replaysS_of_visitedIn`, and
   `*_replaysOn_of_visitedIn` for `f3EmptyMemrchrGhostHook{Ls,,K}` as well as concrete
   `P_sub := pureWordsProg entryTarget coreMemrchrWords` (`f3PureMemrchrGhostHook{Ls,,K}`)
   specializations (`REV-MRO` card-c note).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (memrchrHook)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook
  ghostExternReplaysOn_of_single_stub
  ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
  linkedCallHook_fs_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  withLsRet subroutine_ok_withLsRet withLsRet_pre_setPC withLsRet_outcome_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode (
  masterMemrchrSpec memrchrSpecK
  specStripSInvariant_masterMemrchr specStripSInvariant_masterMemrchrK
  pureWordsProg_memrchr_hasWords
  subroutine_ok_masterMemrchr_of_hasWords
  subroutine_ok_masterMemrchrK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost (
  memrchrGhostFnLs memrchrGhostFn memrchrGhostFnK
  specStripSInvariant_masterMemrchrLs
  specPreservesFsTrace_masterMemrchr specPreservesFsTrace_masterMemrchrLs specPreservesFsTrace_masterMemrchrK
  masterMemrchr_pre_setPC masterMemrchrK_pre_setPC
  masterMemrchr_outcome_setPC masterMemrchrK_outcome_setPC
  memrchrGhostFnLs_keepLr_false_of_noException
  memrchrGhostFnK_keepLr_false_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK (
  f3EmptyMemrchrGhostHookLs f3EmptyMemrchrGhostHook f3EmptyMemrchrGhostHookK
  f3PureMemrchrGhostHookLs f3PureMemrchrGhostHook f3PureMemrchrGhostHookK
  f3EmptyMemrchrGhostHookLs_eq f3EmptyMemrchrGhostHook_eq f3EmptyMemrchrGhostHookK_eq
)

/-! ## 4. Direct `P_real` Guarded Replay (`GhostExternReplaysOn` / `GhostExternReplaysS`) -/

/-- Direct `P_real` per-stub replay for Route `β′` `memrchrGhostFnLs` (`withLsRet masterMemrchrSpec`),
    discharging `keepR (u.readReg64 .lr) = false` automatically from `hKeep` (`K3`) + `hnoex`. -/
theorem memrchrGhostFnLs_replayOn [LibsignalPlacement]
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memrchrGhostFnLs keepR P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memrchrGhostFnLs keepR P_real P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnLs keepR P_real P_sub entryTarget u).mem ∧
      InvMem (memrchrGhostFnLs keepR P_real P_sub entryTarget u).mem ∧
      (memrchrGhostFnLs keepR P_real P_sub entryTarget u).fs = u.fs := by
  have hBase := ghostExternReplaysOn_of_linkedCallHook (fallback := memrchrHook)
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_withLsRet (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords))
    (specStripSInvariant_masterMemrchrLs keepR)
    specPreservesFsTrace_masterMemrchrLs
    (withLsRet_pre_setPC masterMemrchr_pre_setPC)
    (withLsRet_outcome_setPC masterMemrchr_outcome_setPC)
  refine ⟨hBase.1, fun u hpc hrun hnoex hfr hinv => ?_⟩
  have hlr : keepR (u.readReg64 .lr) = false :=
    memrchrGhostFnLs_keepLr_false_of_noException hKeep hnoex
  obtain ⟨hs, hfr', hinv'⟩ := hBase.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv', linkedCallHook_fs_eq u⟩

/-- Direct `P_real` per-stub replay for plain `memrchrGhostFn` (takes `keepR (u.readReg64 .lr) = false`). -/
theorem memrchrGhostFn_replayOn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memrchrGhostFn keepR P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepR (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memrchrGhostFn keepR P_real P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFn keepR P_real P_sub entryTarget u).mem ∧
      InvMem (memrchrGhostFn keepR P_real P_sub entryTarget u).mem ∧
      (memrchrGhostFn keepR P_real P_sub entryTarget u).fs = u.fs := by
  have hBase := ghostExternReplaysOn_of_linkedCallHook (fallback := memrchrHook)
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemrchr keepR)
    specPreservesFsTrace_masterMemrchr
    masterMemrchr_pre_setPC
    masterMemrchr_outcome_setPC
  refine ⟨hBase.1, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hs, hfr', hinv'⟩ := hBase.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv', linkedCallHook_fs_eq u⟩

/-- Direct `P_real` per-stub replay for `K`-narrowed `memrchrGhostFnK` (zero caller `lr` premise). -/
theorem memrchrGhostFnK_replayOn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memrchrGhostFnK keepR P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memrchrGhostFnK keepR P_real P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnK keepR P_real P_sub entryTarget u).mem ∧
      InvMem (memrchrGhostFnK keepR P_real P_sub entryTarget u).mem ∧
      (memrchrGhostFnK keepR P_real P_sub entryTarget u).fs = u.fs := by
  have hBase := ghostExternReplaysOn_of_linkedCallHook (fallback := memrchrHook)
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemrchrK_of_hasWords keepR hsub_no hwords)
    (specStripSInvariant_masterMemrchrK keepR)
    (specPreservesFsTrace_masterMemrchrK keepR)
    (masterMemrchrK_pre_setPC keepR)
    (masterMemrchrK_outcome_setPC keepR)
  refine ⟨hBase.1, fun u hpc hrun hnoex hfr hinv => ?_⟩
  have hlr : keepR (u.readReg64 .lr) = false :=
    memrchrGhostFnK_keepLr_false_of_noException hnoex
  obtain ⟨hs, hfr', hinv'⟩ := hBase.2 u hpc hrun hnoex hfr hlr hinv
  exact ⟨hs, hfr', hinv', linkedCallHook_fs_eq u⟩

/-! ## 5. Stock-Safe `h2fsgen_StepsVisitedIn` First-Stop Witness & `GhostExternReplaysOn` / `S` -/

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop witness for Route `β′`
    `memrchrGhostFnLs` (`keepR (u.readReg64 .lr) = false` discharged from `hKeep` + `hnoex`). -/
theorem memrchrGhostFnLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memrchrGhostFnLs keepR P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget)
        (memrchrGhostFnLs keepR P_run P_sub entryTarget u) ∧
      SubroutineStop u (memrchrGhostFnLs keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnLs keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFnLs keepR P_run P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget)
        (memrchrGhostFnLs keepR P_run P_sub entryTarget u) := by
  classical
  have hlr_out : keepR (u.readReg64 .lr) = false :=
    memrchrGhostFnLs_keepLr_false_of_noException hKeep hnoex
  have hActPre : ActiveRealPre (withLsRet masterMemrchrSpec) u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_withLsRet (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords))
      (specStripSInvariant_masterMemrchrLs keepR)
      specPreservesFsTrace_masterMemrchrLs
      (withLsRet_pre_setPC masterMemrchr_pre_setPC)
      (withLsRet_outcome_setPC masterMemrchr_outcome_setPC)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memrchrGhostFnLs keepR P_run P_sub entryTarget u =
      Classical.choose hReal.2.2.2 := by
    unfold memrchrGhostFnLs linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop witness for plain `memrchrGhostFn`. -/
theorem memrchrGhostFn_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memrchrGhostFn keepR P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget)
        (memrchrGhostFn keepR P_run P_sub entryTarget u) ∧
      SubroutineStop u (memrchrGhostFn keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFn keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFn keepR P_run P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget)
        (memrchrGhostFn keepR P_run P_sub entryTarget u) := by
  classical
  have hActPre : ActiveRealPre masterMemrchrSpec u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords)
      (specStripSInvariant_masterMemrchr keepR)
      specPreservesFsTrace_masterMemrchr
      masterMemrchr_pre_setPC
      masterMemrchr_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memrchrGhostFn keepR P_run P_sub entryTarget u =
      Classical.choose hReal.2.2.2 := by
    unfold memrchrGhostFn linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn keepR P_run` first-stop witness for `memrchrGhostFnK`
    (zero caller `lr` premise). -/
theorem memrchrGhostFnK_visitedIn
    {keepR : BitVec 64 → Bool} {P_run P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (memrchrGhostFnK keepR P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget)
        (memrchrGhostFnK keepR P_run P_sub entryTarget u) ∧
      SubroutineStop u (memrchrGhostFnK keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnK keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFnK keepR P_run P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget)
        (memrchrGhostFnK keepR P_run P_sub entryTarget u) := by
  classical
  have hlr_out : keepR (u.readReg64 .lr) = false :=
    memrchrGhostFnK_keepLr_false_of_noException hnoex
  have hActPre : ActiveRealPre (memrchrSpecK keepR masterMemrchrSpec) u :=
    linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS
      hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterMemrchrK_of_hasWords keepR hsub_no hwords)
      (specStripSInvariant_masterMemrchrK keepR)
      (specPreservesFsTrace_masterMemrchrK keepR)
      (masterMemrchrK_pre_setPC keepR)
      (masterMemrchrK_outcome_setPC keepR)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keepR P_run P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have hfn_eq : memrchrGhostFnK keepR P_run P_sub entryTarget u =
      Classical.choose hReal.2.2.2 := by
    unfold memrchrGhostFnK linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hsf_eq : sf = Classical.choose hReal.2.2.2 :=
    h2fsgen_stepsUntil_det huntil hstop hchoose.1 hchoose.2.1
  rw [hfn_eq, ← hsf_eq]
  exact ⟨huntil, hstop, hfr_sf, hfs, hvis⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` witness for
    `f3EmptyMemrchrGhostHookLs` (Route `β′`). -/
theorem f3EmptyMemrchrGhostHookLs_visitedIn [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) := by
  rw [f3EmptyMemrchrGhostHookLs_eq] at hnoex ⊢
  exact memrchrGhostFnLs_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hKeep
    hrun hnoex hFr hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` witness for
    `f3EmptyMemrchrGhostHook`. -/
theorem f3EmptyMemrchrGhostHook_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keepR (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u) := by
  rw [f3EmptyMemrchrGhostHook_eq] at hnoex ⊢
  exact memrchrGhostFn_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    hrun hnoex hFr hlr_out hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keepR emptyStdProg` witness for
    `f3EmptyMemrchrGhostHookK` (zero caller `lr` premise). -/
theorem f3EmptyMemrchrGhostHookK_visitedIn
    {keepR : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keepR u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).fs = u.fs ∧
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget)
        (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) := by
  rw [f3EmptyMemrchrGhostHookK_eq] at hnoex ⊢
  exact memrchrGhostFnK_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hrun hnoex hFr
    hCodeSub

/-- Memory-guarded `P_run → P_real` replay for Route `β′` `memrchrGhostFnLs` via `hLiftVis`
    (discharging `keepR (u.readReg64 .lr) = false` from `hKeep`, zero per-call `lr` premise). -/
theorem memrchrGhostFnLs_replayOn_of_visitedIn [LibsignalPlacement]
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memrchrGhostFnLs keepR P_run P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memrchrGhostFnLs keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnLs keepR P_run P_sub entryTarget u).mem ∧
      InvMem (memrchrGhostFnLs keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFnLs keepR P_run P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨_, _, hfr_sf, hfs_sf, hvis⟩ :=
    memrchrGhostFnLs_visitedIn hsvc_run hsvc_sub hrun_no hsub_no hwords hKeep
      hrun hnoex hfr (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (memrchrGhostFnLs keepR P_run P_sub entryTarget u) :=
    hLiftVis u _ hrun hfr hinv hvis
  have hSteps : Steps P_real u (memrchrGhostFnLs keepR P_run P_sub entryTarget u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Memory-guarded `P_run → P_real` replay for plain `memrchrGhostFn` via `hLiftVis`. -/
theorem memrchrGhostFn_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memrchrGhostFn keepR P_run P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepR (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memrchrGhostFn keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFn keepR P_run P_sub entryTarget u).mem ∧
      InvMem (memrchrGhostFn keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFn keepR P_run P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨_, _, hfr_sf, hfs_sf, hvis⟩ :=
    memrchrGhostFn_visitedIn hsvc_run hsvc_sub hrun_no hsub_no hwords
      hrun hnoex hfr hlr (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (memrchrGhostFn keepR P_run P_sub entryTarget u) :=
    hLiftVis u _ hrun hfr hinv hvis
  have hSteps : Steps P_real u (memrchrGhostFn keepR P_run P_sub entryTarget u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Memory-guarded `P_run → P_real` replay for `memrchrGhostFnK` via `hLiftVis`
    (zero caller `lr` premise). -/
theorem memrchrGhostFnK_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keepR pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR P_run (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memrchrGhostFnK keepR P_run P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memrchrGhostFnK keepR P_run P_sub entryTarget u) ∧
      ExecFrozen (memrchrGhostFnK keepR P_run P_sub entryTarget u).mem ∧
      InvMem (memrchrGhostFnK keepR P_run P_sub entryTarget u).mem ∧
      (memrchrGhostFnK keepR P_run P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨_, _, hfr_sf, hfs_sf, hvis⟩ :=
    memrchrGhostFnK_visitedIn hsvc_run hsvc_sub hrun_no hsub_no hwords
      hrun hnoex hfr (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (memrchrGhostFnK keepR P_run P_sub entryTarget u) :=
    hLiftVis u _ hrun hfr hinv hvis
  have hSteps : Steps P_real u (memrchrGhostFnK keepR P_run P_sub entryTarget u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- `emptyStdProg → P_real` replay for Route `β′` `f3EmptyMemrchrGhostHookLs` via `hLiftVis`. -/
theorem f3EmptyMemrchrGhostHookLs_replayOn_of_visitedIn [LibsignalPlacement]
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget u).fs = u.fs := by
  simp only [f3EmptyMemrchrGhostHookLs_eq]
  exact memrchrGhostFnLs_replayOn_of_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords hKeep
    hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- `emptyStdProg → P_real` replay for plain `f3EmptyMemrchrGhostHook` via `hLiftVis`. -/
theorem f3EmptyMemrchrGhostHook_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepR (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHook keepR P_sub entryTarget u).fs = u.fs := by
  simp only [f3EmptyMemrchrGhostHook_eq]
  exact memrchrGhostFn_replayOn_of_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- `emptyStdProg → P_real` replay for `f3EmptyMemrchrGhostHookK` via `hLiftVis`. -/
theorem f3EmptyMemrchrGhostHookK_replayOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).mem ∧
      (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget u).fs = u.fs := by
  simp only [f3EmptyMemrchrGhostHookK_eq]
  exact memrchrGhostFnK_replayOn_of_visitedIn rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- `f3PureMemrchrGhostHookLs` (`P_sub := pureWordsProg entryTarget coreMemrchrWords`) specialization
    of `f3EmptyMemrchrGhostHookLs_replayOn_of_visitedIn` (`REV-MRO` card-c note). -/
theorem f3PureMemrchrGhostHookLs_replayOn_of_visitedIn [LibsignalPlacement]
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_real : Program}
    {stubPc entryTarget : BitVec 64}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg entryTarget coreMemrchrWords).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3PureMemrchrGhostHookLs keepR entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f3PureMemrchrGhostHookLs keepR entryTarget u) ∧
      ExecFrozen (f3PureMemrchrGhostHookLs keepR entryTarget u).mem ∧
      InvMem (f3PureMemrchrGhostHookLs keepR entryTarget u).mem ∧
      (f3PureMemrchrGhostHookLs keepR entryTarget u).fs = u.fs :=
  f3EmptyMemrchrGhostHookLs_replayOn_of_visitedIn rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)
    hKeep hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- Single-row `GhostExternReplaysS` for Route `β′` `f3EmptyMemrchrGhostHookLs` (polymorphic in
    outer `keep_any` since `hKeep` discharges `keepR lr = false`). -/
theorem f3EmptyMemrchrGhostHookLs_replaysS_of_visitedIn [LibsignalPlacement]
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemrchrGhostHookLs_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords hKeep hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Trajectory-aware single-row `GhostExternReplaysOn` for Route `β′` `f3EmptyMemrchrGhostHookLs`
    (polymorphic in outer `keep_any`). -/
theorem f3EmptyMemrchrGhostHookLs_replaysOn_of_visitedIn [LibsignalPlacement]
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program} {s0 sf : State}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemrchrGhostHookLs keepR P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf' →
      Steps P_real (u.setPC entryTarget) sf') :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := f3EmptyMemrchrGhostHookLs_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords hKeep hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ _ hpc hrun hnoex _ hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS` for plain `f3EmptyMemrchrGhostHook`. -/
theorem f3EmptyMemrchrGhostHook_replaysS_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemrchrGhostHook keepR P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keepR (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemrchrGhostHook_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Trajectory-aware single-row `GhostExternReplaysOn` for plain `f3EmptyMemrchrGhostHook`. -/
theorem f3EmptyMemrchrGhostHook_replaysOn_of_visitedIn
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program} {s0 sf : State}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemrchrGhostHook keepR P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf' →
      Steps P_real (u.setPC entryTarget) sf') :
    GhostExternReplaysOn keepR (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := f3EmptyMemrchrGhostHook_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ _ hpc hrun hnoex _ hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS` for `K`-narrowed `f3EmptyMemrchrGhostHookK` (polymorphic in
    outer `keep_any`). -/
theorem f3EmptyMemrchrGhostHookK_replaysS_of_visitedIn
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemrchrGhostHookK_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Trajectory-aware single-row `GhostExternReplaysOn` for `K`-narrowed `f3EmptyMemrchrGhostHookK`
    (polymorphic in outer `keep_any`). -/
theorem f3EmptyMemrchrGhostHookK_replaysOn_of_visitedIn
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real P_sub : Program} {s0 sf : State}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemrchrGhostHookK keepR P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget coreMemrchrWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf' →
      Steps P_real (u.setPC entryTarget) sf') :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := f3EmptyMemrchrGhostHookK_replayOn_of_visitedIn
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ _ hpc hrun hnoex _ hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS` for concrete `f3PureMemrchrGhostHookLs`
    (`P_sub := pureWordsProg entryTarget coreMemrchrWords`, `REV-MRO` card-c note). -/
theorem f3PureMemrchrGhostHookLs_replaysS_of_visitedIn [LibsignalPlacement]
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3PureMemrchrGhostHookLs keepR entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg entryTarget coreMemrchrWords).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real :=
  f3EmptyMemrchrGhostHookLs_replaysS_of_visitedIn keep_any hghost_stub hother hreal_fr rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)
    hKeep hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- Trajectory-aware single-row `GhostExternReplaysOn` for concrete `f3PureMemrchrGhostHookLs`
    (`P_sub := pureWordsProg entryTarget coreMemrchrWords`, `REV-MRO` card-c note). -/
theorem f3PureMemrchrGhostHookLs_replaysOn_of_visitedIn [LibsignalPlacement]
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keepR : BitVec 64 → Bool} {P_ghost P_real : Program} {s0 sf : State}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3PureMemrchrGhostHookLs keepR entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg entryTarget coreMemrchrWords).CodeLoaded (stripExecOutside keepR mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State,
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      h2fsgen_StepsVisitedIn keepR emptyStdProg (u.setPC entryTarget) sf' →
      Steps P_real (u.setPC entryTarget) sf') :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf :=
  f3EmptyMemrchrGhostHookLs_replaysOn_of_visitedIn keep_any hghost_stub hother hreal_fr rfl
    (pureWordsProg_externAt_none entryTarget coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entryTarget)
    hKeep hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn
