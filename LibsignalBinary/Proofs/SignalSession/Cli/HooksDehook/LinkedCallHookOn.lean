/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import

/-!
# Memory-Guarded `linkedCallHook` Replay Helpers (`HooksDehook.LinkedCallHookOn`)

Symbol-generic (`memset`-, `memcpy`-, and `memcmp`-independent) memory-guarded `On` / `S`
replacements for `AllocGhostLinkTransfer.ghostExternReplays_of_linkedCallHook`:

1. **`ghostExternReplaysOn_of_linkedCallHook`**:
   Replaces the unguarded `StubReachesTarget P_real stubPc entryTarget` premise (unsatisfiable when
   `stubPc ≠ entryTarget`, e.g. `--branch-stubs` 4-byte `b target` stubs where empty memory steps
   via `Step.halt_unmapped`) with `StubReachesTargetOn InvMem P_real stubPc entryTarget`
   (`Ghost617Transfer.stubReachesTargetOn_of_directOrBranchStub`), `hInvLoaded`, and `hInvKf`,
   establishing the exact `GhostExternReplaysS` / `GhostExternReplaysOn` `none`-branch shape:
   `Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvMem (f u).mem`.
2. **`linkedCallHook_fs_eq`**:
   Filesystem invariance `(linkedCallHook ... u).fs = u.fs` whenever `(fallback u).fs = u.fs` (true
   by `rfl` for pure memory hooks such as `hookMemset`, `hookMemcpy`, and `hookBcmp`).
3. **`ghostExternReplaysS_of_single_stub` & `ghostExternReplaysOn_of_single_stub`**:
   Generic single-stub overlay packagers lifting a per-stub replay into a full
   `GhostExternReplaysS keep InvS P_ghost P_real` or
   `GhostExternReplaysOn keep InvS P_ghost P_real s0 sf` witness whenever `P_ghost.externAt?`
   differs from `P_real.externAt?` only at `stubPc`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn

open Arm64 ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace_fs linkedCallHook linkedCallHook_active_steps
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)

/-! ## 1. Generic Memory-Guarded `linkedCallHook` Replay (`On` / `S` Shape) -/

/-- Any non-`.Exception` evaluation of `linkedCallHook` must have entered the `ActiveRealPre`
    branch (since the `¬ ActiveRealPre` branch returns `.Exception "ghost-hook precondition violated"`). -/
theorem linkedCallHook_activeRealPre_of_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    {u : State}
    (hnoex : ∀ msg,
      (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) :
    ActiveRealPre spec u := by
  classical
  by_contra hNotPre
  apply hnoex "ghost-hook precondition violated"
  unfold linkedCallHook
  simp [hNotPre]

/-- Unconditional `.fs` invariance of `linkedCallHook`: the `ActiveRealRun` witness branch
    preserves `u.fs` (`sf.fs = u.fs`), the fallback branch wraps `fallback` in `keepFsTrace`
    (`rfl`), and the `.Exception` guard branch preserves `u.fs` (`rfl`). -/
theorem linkedCallHook_fs_eq {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (u : State) :
    (linkedCallHook keep P_real P_sub entryTarget spec fallback u).fs = u.fs := by
  classical
  unfold linkedCallHook
  by_cases hPre : ActiveRealPre spec u
  · by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget u
    · simp only [hPre, hReal, ↓reduceDIte]
      exact (Classical.choose_spec hReal.2.2.2).2.2.1
    · simp only [hPre, hReal, ↓reduceDIte]
      exact keepFsTrace_fs fallback u
  · simp [hPre]

/-- **Memory-guarded `On`/`S` replacement for `ghostExternReplays_of_linkedCallHook`:**
    Given `hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget`, `hInvLoaded`, and
    `KeepsFrozen`-stability `hInvKf` of `InvMem`, every non-faulting ghost call to
    `f := linkedCallHook keep P_real P_sub entryTarget spec fallback` at `stubPc` with
    `ExecFrozen u.mem`, `keep (u.readReg64 .lr) = false`, and `InvMem u.mem` replays as real
    machine steps `Steps P_real u (f u)` preserving both `ExecFrozen (f u).mem` and
    `InvMem (f u).mem`. -/
theorem ghostExternReplaysOn_of_linkedCallHook {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hActPre : ActiveRealPre spec u := linkedCallHook_activeRealPre_of_noException hnoex
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvLoaded u.mem hfr hinv
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  obtain ⟨hBodySteps, hfr_out⟩ :=
    linkedCallHook_active_steps hsvc_real hsvc_sub hreal_no hsub_no hOk hInv hFsT
      hPrePC hOutPC hActPre hfr hlr hCodeSub
  have hSteps : Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_out, hInvKf u.mem _ hinv hSteps.keepsFrozen⟩

/-! ## 2. Generic Single-Stub `GhostExternReplaysS` & `GhostExternReplaysOn` Packagers -/

/-- Package a per-stub `On` replay for `f_stub` into a full trajectory-independent
    `GhostExternReplaysS keep InvS P_ghost P_real` witness when `P_ghost.externAt?` agrees with
    `P_real.externAt?` everywhere except `stubPc`.
    *Applicability note (`rev_c6` F2):* `hother` assumes a single ghost/real mismatch (`stubPc`),
    covering a single-symbol pass rather than a multi-row CLI ghost table (`8` ghost rows); multi-row
    K CLI passes assemble per-PC replays directly from `ghostExternReplaysOn_of_linkedCallHook`. -/
theorem ghostExternReplaysS_of_single_stub
    {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {P_ghost P_real : Program} {stubPc : BitVec 64} {f_stub : State → State}
    (hghost_stub : P_ghost.externAt? stubPc = some f_stub)
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem → InvS u → ExecFrozen (f u).mem ∧ InvS (f u))
    (hstub_replay : P_real.externAt? stubPc = none ∧
      ∀ u : State,
        u.pc = stubPc →
        u.status = .Running →
        (∀ msg, (f_stub u).status ≠ .Exception msg) →
        ExecFrozen u.mem →
        keep (u.readReg64 .lr) = false →
        InvS u →
        Steps P_real u (f_stub u) ∧ ExecFrozen (f_stub u).mem ∧ InvS (f_stub u)) :
    GhostExternReplaysS keep InvS P_ghost P_real := by
  intro pc f hg
  by_cases hpc : pc = stubPc
  · subst hpc
    rw [hghost_stub] at hg
    injection hg with hfeq
    subst hfeq
    exact Or.inr hstub_replay
  · have hr : P_real.externAt? pc = some f := by
      rw [← hother pc hpc]
      exact hg
    exact Or.inl ⟨hr, hreal_pres pc f hr⟩

/-- Package a trajectory-aware per-stub `On` replay for `f_stub` into a full
    `GhostExternReplaysOn keep InvS P_ghost P_real s0 sf` witness when `P_ghost.externAt?` agrees
    with `P_real.externAt?` everywhere except `stubPc`.
    *Applicability note (`rev_c6` F2):* `hother` assumes a single ghost/real mismatch (`stubPc`),
    covering a single-symbol pass rather than a multi-row CLI ghost table (`8` ghost rows). -/
theorem ghostExternReplaysOn_of_single_stub
    {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {P_ghost P_real : Program} {s0 sf : State}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hghost_stub : P_ghost.externAt? stubPc = some f_stub)
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State,
        Steps P_ghost s0 u →
        Steps P_ghost (f u) sf →
        u.pc = pc →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        InvS u →
        ExecFrozen (f u).mem ∧ InvS (f u))
    (hstub_replay : P_real.externAt? stubPc = none ∧
      ∀ u : State,
        Steps P_ghost s0 u →
        Steps P_ghost (f_stub u) sf →
        u.pc = stubPc →
        u.status = .Running →
        (∀ msg, (f_stub u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f_stub u).mem →
        ExecFrozen u.mem →
        keep (u.readReg64 .lr) = false →
        InvS u →
        Steps P_real u (f_stub u) ∧ ExecFrozen (f_stub u).mem ∧ InvS (f_stub u)) :
    GhostExternReplaysOn keep InvS P_ghost P_real s0 sf := by
  intro pc f hg
  by_cases hpc : pc = stubPc
  · subst hpc
    rw [hghost_stub] at hg
    injection hg with hfeq
    subst hfeq
    exact Or.inr hstub_replay
  · have hr : P_real.externAt? pc = some f := by
      rw [← hother pc hpc]
      exact hg
    exact Or.inl ⟨hr, hreal_pres pc f hr⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
