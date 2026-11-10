/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays -- proof-setup: allow-public-import

/-!
# Memory-Guarded `On` / `S` Replays, `Returned` Transfers & `W`-Independent Core (`HooksDehook.MemcpyGhostReplaysOn`)

Mirrors `HooksDehook.MemsetGhostReplaysOn` and the replay half of `HooksDehook.MemsetGhostK`
(`ba4d2cc002`) for `memcpy` (`mallocngLib` block 20, `396` B at `mmpl.base 20`), using **only**
memory-guarded `StubReachesTargetOn InvMem` (never unguarded `StubReachesTarget`):

1. **Per-Stub Guarded `On` Replays (`StubReachesTargetOn InvMem`)**:
   Instantiates `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook` for `memcpyGhostHook`,
   `memcpyGhostHookK` (explicit-`lr` and `noException`-auto-`lr`), `memcpyGhostHookBlk20[K]`,
   `f3MemcpyGhostHook[K]`, `f3MemcpyGhostHookNarrow[K]`, and `f3MemcpyGhostHookRange[K]`.
2. **Single-Row `GhostExternReplaysS` Packagers**:
   Trajectory-independent `GhostExternReplaysS` witnesses for `memcpyGhostHook`,
   `memcpyGhostHookK` (polymorphic in outer `keep_any`), and `f3MemcpyGhostHookNarrow`.
3. **Closed-Trap `_of_trap_ret` Guarded `On` Replays & `Steps` Transfer (Including `Returned`)**:
   Discharges `keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false` internally via
   `MemcpyLrTrapRet.blk20_lr_trap_after_hook_ret` under `(A1)` + `(A2)`, plus
   `steps_transfer_memcpyGhostHookNarrow_On_returned` / `steps_transfer_f3MemcpyGhostHookNarrow_On_returned`.
4. **`W`-Independent K-Convention Core (`f3EmptyMemcpyGhostHook`, `f3EmptyMemcpyGhostHookK`)**:
   Defined with `F3AllocStdinGhostHooks.f3LinkedCallHook` at `P_real := emptyStdProg`, with
   `StepsUntil emptyStdProg` first-stop witnesses and `emptyStdProg → P_real` guarded replay lifts.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memcpySymWords)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealRun ExecFrozen real_subroutine_run_of_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn steps_transfer_ghostOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook ghostExternReplaysOn_of_single_stub
  ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  activeF3CallPre_const_iff emptyStdProg f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  codeLoaded_stripExecOutside_of_keep f3RealProg617 f3RealProg617_svc_eq keepRange
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords
  masterMemcpySpec memcpySpecK
  subroutine_ok_masterMemcpy_of_hasWords subroutine_ok_masterMemcpyK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  KeepCoversBlk20 keepCoversBlk20_keepMemcpyBlk20 keepCoversBlk20_of_range keepMemcpyBlk20
  masterMemcpy_outcome_setPC masterMemcpy_pre_setPC
  masterMemcpyK_outcome_setPC masterMemcpyK_pre_setPC
  memcpyGhostHook memcpyGhostHookBlk20 memcpyGhostHookBlk20K memcpyGhostHookK
  memcpyGhostHookK_keepLr_false_of_noException
  specPreservesFsTrace_masterMemcpy specPreservesFsTrace_masterMemcpyK
  specStripSInvariant_masterMemcpy specStripSInvariant_masterMemcpyK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap (
  mallocngBlockProg20_code_length
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet (
  Blk20TrapHook blk20TrapHook_memcpyGhostHook_of_cover blk20_lr_trap_after_hook_ret
  blk20_lr_trap_false_ret
)

/-! ## 0. Concrete `blk20` / `f3RealProg617` Helpers & `CodeLoaded` Lifting -/

theorem mallocngBlockProg20_svc_eq (mmpl : Obj.MultiPlacement) :
    (mallocngBlockProg mmpl 20 Syscall.standard).svc = Syscall.standard := rfl

theorem codeLoaded_stripExecOutside_blk20
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} {m : Memory}
    (hkeep : KeepCoversBlk20 keep mmpl)
    (hL : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m) :
    (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded (stripExecOutside keep m) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  rw [mallocngBlockProg20_code_length] at hoff
  exact hkeep off hoff

theorem keepCoversBlk20_keepRange {mmpl : Obj.MultiPlacement} (lo hi : Nat)
    (hlo : lo ≤ (mmpl.base 20).toNat)
    (hhi : (mmpl.base 20).toNat + 396 ≤ hi)
    (hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64) :
    KeepCoversBlk20 (keepRange lo hi) mmpl :=
  keepCoversBlk20_of_range lo hi
    (fun _ h1 h2 => decide_eq_true ⟨h1, h2⟩) hlo hhi hnowrap

noncomputable abbrev f3MemcpyGhostHook
    (keep : BitVec 64 → Bool) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  memcpyGhostHookBlk20 keep (f3RealProg617 mpl mmpl W) mmpl

noncomputable abbrev f3MemcpyGhostHookK
    (keep : BitVec 64 → Bool) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  memcpyGhostHookBlk20K keep (f3RealProg617 mpl mmpl W) mmpl

noncomputable abbrev f3MemcpyGhostHookNarrow
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemcpyGhostHook (keepMemcpyBlk20 mmpl) mpl mmpl W

noncomputable abbrev f3MemcpyGhostHookNarrowK
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemcpyGhostHookK (keepMemcpyBlk20 mmpl) mpl mmpl W

noncomputable abbrev f3MemcpyGhostHookRange
    (lo hi : Nat) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemcpyGhostHook (keepRange lo hi) mpl mmpl W

noncomputable abbrev f3MemcpyGhostHookRangeK
    (lo hi : Nat) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemcpyGhostHookK (keepRange lo hi) mpl mmpl W

/-! ## 1. Per-Stub Memory-Guarded `On` Replays (`StubReachesTargetOn InvMem`) -/

/-- Generic memory-guarded `On` replay for plain `memcpyGhostHook`. -/
theorem ghostExternReplaysOn_memcpyGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memcpyGhostHook keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memcpyGhostHook keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memcpyGhostHook keep P_real P_sub entryTarget u).mem ∧
      InvMem (memcpyGhostHook keep P_real P_sub entryTarget u).mem :=
  ghostExternReplaysOn_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemcpy_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemcpy keep)
    specPreservesFsTrace_masterMemcpy
    masterMemcpy_pre_setPC
    masterMemcpy_outcome_setPC

/-- Generic memory-guarded `On` replay for `K`-narrowed `memcpyGhostHookK` (explicit `hlr`). -/
theorem ghostExternReplaysOn_memcpyGhostHookK
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memcpyGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memcpyGhostHookK keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memcpyGhostHookK keep P_real P_sub entryTarget u).mem ∧
      InvMem (memcpyGhostHookK keep P_real P_sub entryTarget u).mem :=
  ghostExternReplaysOn_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemcpyK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemcpyK keep)
    (specPreservesFsTrace_masterMemcpyK keep)
    (masterMemcpyK_pre_setPC keep)
    (masterMemcpyK_outcome_setPC keep)

/-- Memory-guarded `On` replay for `memcpyGhostHookK` with **zero caller `lr` premise**
    (`keep (u.readReg64 .lr) = false` discharged automatically from `hnoex`). -/
theorem ghostExternReplaysOn_memcpyGhostHookK_autoLr
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memcpyGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memcpyGhostHookK keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memcpyGhostHookK keep P_real P_sub entryTarget u).mem ∧
      InvMem (memcpyGhostHookK keep P_real P_sub entryTarget u).mem := by
  have hRep := ghostExternReplaysOn_memcpyGhostHookK
    hsvc_real hsvc_sub hreal_no hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf
  exact ⟨hRep.1, fun u hpc hrun hnoex hfr hinv =>
    hRep.2 u hpc hrun hnoex hfr (memcpyGhostHookK_keepLr_false_of_noException hnoex) hinv⟩

/-- `blk20`-specialized memory-guarded `On` replay for `memcpyGhostHookBlk20`. -/
theorem ghostExternReplaysOn_memcpyGhostHookBlk20
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk20 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memcpyGhostHookBlk20 keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memcpyGhostHookBlk20 keep P_real mmpl u) ∧
      ExecFrozen (memcpyGhostHookBlk20 keep P_real mmpl u).mem ∧
      InvMem (memcpyGhostHookBlk20 keep P_real mmpl u).mem :=
  ghostExternReplaysOn_memcpyGhostHook
    hsvc_real (mallocngBlockProg20_svc_eq mmpl) hreal_no
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)
    hreal_stub_none hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk20 hcover (hInvLoaded m hfr hinv))
    hInvKf

/-- `blk20`-specialized memory-guarded `On` replay for `memcpyGhostHookBlk20K` (explicit `hlr`). -/
theorem ghostExternReplaysOn_memcpyGhostHookBlk20K
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk20 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memcpyGhostHookBlk20K keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memcpyGhostHookBlk20K keep P_real mmpl u) ∧
      ExecFrozen (memcpyGhostHookBlk20K keep P_real mmpl u).mem ∧
      InvMem (memcpyGhostHookBlk20K keep P_real mmpl u).mem :=
  ghostExternReplaysOn_memcpyGhostHookK
    hsvc_real (mallocngBlockProg20_svc_eq mmpl) hreal_no
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)
    hreal_stub_none hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk20 hcover (hInvLoaded m hfr hinv))
    hInvKf

/-- `blk20`-specialized memory-guarded `On` replay for `memcpyGhostHookBlk20K` (auto-`lr`). -/
theorem ghostExternReplaysOn_memcpyGhostHookBlk20K_autoLr
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk20 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memcpyGhostHookBlk20K keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memcpyGhostHookBlk20K keep P_real mmpl u) ∧
      ExecFrozen (memcpyGhostHookBlk20K keep P_real mmpl u).mem ∧
      InvMem (memcpyGhostHookBlk20K keep P_real mmpl u).mem := by
  have hRep := ghostExternReplaysOn_memcpyGhostHookBlk20K
    hsvc_real hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf
  exact ⟨hRep.1, fun u hpc hrun hnoex hfr hinv =>
    hRep.2 u hpc hrun hnoex hfr (memcpyGhostHookK_keepLr_false_of_noException hnoex) hinv⟩

/-- Guarded `On` replay for `f3MemcpyGhostHook` (`P_real := f3RealProg617 mpl mmpl W`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {mpl mmpl : Obj.MultiPlacement}
    {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hcover : KeepCoversBlk20 keep mmpl)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHook keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHook keep mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHook keep mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHook keep mpl mmpl W u).mem :=
  ghostExternReplaysOn_memcpyGhostHookBlk20
    (f3RealProg617_svc_eq mpl mmpl W) hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemcpyGhostHookK` (explicit `hlr`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookK
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {mpl mmpl : Obj.MultiPlacement}
    {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hcover : KeepCoversBlk20 keep mmpl)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookK keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookK keep mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookK keep mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookK keep mpl mmpl W u).mem :=
  ghostExternReplaysOn_memcpyGhostHookBlk20K
    (f3RealProg617_svc_eq mpl mmpl W) hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemcpyGhostHookK` (auto-`lr`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookK_autoLr
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {mpl mmpl : Obj.MultiPlacement}
    {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hcover : KeepCoversBlk20 keep mmpl)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookK keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookK keep mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookK keep mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookK keep mpl mmpl W u).mem :=
  ghostExternReplaysOn_memcpyGhostHookBlk20K_autoLr
    (f3RealProg617_svc_eq mpl mmpl W) hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemcpyGhostHookNarrow` (`keep := keepMemcpyBlk20 mmpl`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookNarrow
    {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookNarrow mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookNarrow mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemcpyGhostHook
    hreal_no (keepCoversBlk20_keepMemcpyBlk20 mmpl) hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemcpyGhostHookNarrowK` (auto-`lr`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookNarrowK_autoLr
    {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookNarrowK mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookNarrowK mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookNarrowK mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookNarrowK mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemcpyGhostHookK_autoLr
    hreal_no (keepCoversBlk20_keepMemcpyBlk20 mmpl) hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemcpyGhostHookRange` (`keep := keepRange lo hi`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookRange
    {lo hi : Nat} {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hlo : lo ≤ (mmpl.base 20).toNat)
    (hhi : (mmpl.base 20).toNat + 396 ≤ hi)
    (hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64)
    (hreal_no : ∀ pc, keepRange lo hi pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookRange lo hi mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepRange lo hi (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookRange lo hi mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookRange lo hi mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookRange lo hi mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemcpyGhostHook
    hreal_no (keepCoversBlk20_keepRange lo hi hlo hhi hnowrap)
    hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemcpyGhostHookRangeK` (auto-`lr`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookRangeK_autoLr
    {lo hi : Nat} {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hlo : lo ≤ (mmpl.base 20).toNat)
    (hhi : (mmpl.base 20).toNat + 396 ≤ hi)
    (hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64)
    (hreal_no : ∀ pc, keepRange lo hi pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookRangeK lo hi mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookRangeK lo hi mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookRangeK lo hi mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookRangeK lo hi mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemcpyGhostHookK_autoLr
    hreal_no (keepCoversBlk20_keepRange lo hi hlo hhi hnowrap)
    hreal_stub_none hStub hInvLoaded hInvKf

/-! ## 2. Single-Row `GhostExternReplaysS` Packagers -/

/-- Single-row `GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real` for plain
    `memcpyGhostHook`. -/
theorem ghostExternReplaysS_memcpyGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memcpyGhostHook keep P_real P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real :=
  ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    (ghostExternReplaysOn_memcpyGhostHook
      hsvc_real hsvc_sub hreal_no hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf)

/-- Single-row `GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real` for
    `memcpyGhostHookK` (polymorphic in `keep_any` because `keep (u.readReg64 .lr) = false` is
    discharged internally from `hnoex`). -/
theorem ghostExternReplaysS_memcpyGhostHookK
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memcpyGhostHookK keep P_real P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := ghostExternReplaysOn_memcpyGhostHookK_autoLr
    hsvc_real hsvc_sub hreal_no hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv => hRep.2 u hpc hrun hnoex hfr hinv⟩

/-- Single-row `GhostExternReplaysS (keepMemcpyBlk20 mmpl) (fun u => InvMem u.mem)` for
    `f3MemcpyGhostHookNarrow` over `f3RealProg617 mpl mmpl W`. -/
theorem ghostExternReplaysS_f3MemcpyGhostHookNarrow
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc = some (f3MemcpyGhostHookNarrow mpl mmpl W))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (f3RealProg617 mpl mmpl W).externAt? pc)
    (hreal_fr : ∀ pc f, (f3RealProg617 mpl mmpl W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS (keepMemcpyBlk20 mmpl) (fun u => InvMem u.mem) P_ghost
      (f3RealProg617 mpl mmpl W) :=
  ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    (ghostExternReplaysOn_f3MemcpyGhostHookNarrow
      hreal_no hreal_stub_none hStub hInvLoaded hInvKf)

/-! ## 3. `(A1)` + `(A2)` Closed-Trap `_of_trap_ret` Guarded `On` Replays & `Steps` Transfer -/

/-- Per-stub `(A1)` + `(A2)` trap-discharged guarded `On` replay for `memcpyGhostHookBlk20`
    at `keep := keepMemcpyBlk20 mmpl`. -/
theorem ghostExternReplaysOn_memcpyGhostHookNarrow_of_trap_ret
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let f_mc := memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl) P_real mmpl
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f_mc u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f_mc u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f_mc u).mem →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f_mc u) ∧ ExecFrozen (f_mc u).mem ∧ InvMem (f_mc u).mem := by
  have hRep := ghostExternReplaysOn_memcpyGhostHookBlk20
    hsvc_real hreal_no (keepCoversBlk20_keepMemcpyBlk20 mmpl)
    hreal_stub_none hStub hInvLoaded hInvKf
  refine ⟨hRep.1, fun u hrest hpc hrun hnoex hkf hfr hinv => ?_⟩
  have hlr_false : keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
    blk20_lr_trap_after_hook_ret
      (blk20TrapHook_memcpyGhostHook_of_cover (fun _ h => h) P_real
        (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20))
      hblk20_ext
      ((hInvLoaded u.mem hfr hinv).of_keepsFrozen hkf)
      hrest hrun hrun_sf' hnoex_sf hnhalt_sf
  exact hRep.2 u hpc hrun hnoex hfr hlr_false hinv

/-- `f3RealProg617` specialization (`ghostExternReplaysOn_f3MemcpyGhostHookNarrow_of_trap_ret`). -/
theorem ghostExternReplaysOn_f3MemcpyGhostHookNarrow_of_trap_ret
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f3MemcpyGhostHookNarrow mpl mmpl W u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemcpyGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f3MemcpyGhostHookNarrow mpl mmpl W u).mem →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemcpyGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemcpyGhostHookNarrow mpl mmpl W u).mem ∧
      InvMem (f3MemcpyGhostHookNarrow mpl mmpl W u).mem :=
  ghostExternReplaysOn_memcpyGhostHookNarrow_of_trap_ret
    hblk20_ext (f3RealProg617_svc_eq mpl mmpl W) hreal_no hreal_stub_none hStub hInvLoaded hInvKf
    hrun_sf' hnoex_sf hnhalt_sf

/-- Single-stub `GhostExternReplaysOn` from `(A1)` + `(A2)` (`keep_any`-polymorphic). -/
theorem ghostExternReplaysOn_single_memcpyGhostHookNarrow_of_trap_ret
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    {s0 sf : State}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl) P_real mmpl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := ghostExternReplaysOn_memcpyGhostHookNarrow_of_trap_ret
    hblk20_ext hsvc_real hreal_no hreal_stub_none hStub hInvLoaded hInvKf
    hrun_sf' hnoex_sf hnhalt_sf
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ hrest hpc hrun hnoex hkf hfr _ hinv =>
      hRep.2 u hrest hpc hrun hnoex hkf hfr hinv⟩

/-- End-to-End single-stub guarded `Steps` cutover (`steps_transfer_memcpyGhostHookNarrow_On_ret`). -/
theorem steps_transfer_memcpyGhostHookNarrow_On_ret
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl) P_real mmpl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem) :
    Steps P_real s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem := by
  have hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none := by
    intro pc hgn
    by_cases hpc : pc = stubPc
    · subst hpc; exact hreal_stub_none
    · rw [← hother pc hpc]; exact hgn
  have hReplays : GhostExternReplaysOn (fun _ => false) (fun u => InvMem u.mem)
      P_ghost P_real s0 sf :=
    ghostExternReplaysOn_single_memcpyGhostHookNarrow_of_trap_ret (fun _ => false)
      hblk20_ext hghost_stub hother hreal_fr hsvc_real hreal_no hreal_stub_none
      hStub hInvLoaded hInvKf hrun_sf' hnoex_sf hnhalt_sf
  exact steps_transfer_ghostOn hsvc_ghost hsvc_real hno_new_hooks hsteps hnoex_sf hnhalt_sf
    hfr0 hinv0 hReplays
    (fun z _ _ _ _ _ _ _ hkf _ hinv => hInvKf z.mem _ hinv hkf)
    (fun z _ _ _ _ _ hkf _ hinv => hInvKf z.mem _ hinv hkf)
    (fun _ _ _ _ _ => rfl)

/-- `f3RealProg617` specialization of `steps_transfer_memcpyGhostHookNarrow_On_ret`. -/
theorem steps_transfer_f3MemcpyGhostHookNarrow_On_ret
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc = some (f3MemcpyGhostHookNarrow mpl mmpl W))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (f3RealProg617 mpl mmpl W).externAt? pc)
    (hreal_fr : ∀ pc f, (f3RealProg617 mpl mmpl W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem) :
    Steps (f3RealProg617 mpl mmpl W) s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem :=
  steps_transfer_memcpyGhostHookNarrow_On_ret
    hsvc_ghost (f3RealProg617_svc_eq mpl mmpl W) hblk20_ext hghost_stub hother hreal_fr
    hreal_no hreal_stub_none hStub hInvLoaded hInvKf hsteps hrun_sf' hnoex_sf hnhalt_sf hfr0 hinv0

/-- Subroutine `Returned` specialization of `(A1)` + `(A2)` `hlr_calls` (`blk20_lr_trap_false_returned`). -/
theorem blk20_lr_trap_false_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_ne_stub : s0.readReg64 .lr ≠ stubPc)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_ret hblk20_ext hmis_trap hc_codeLoaded
    (fun hr => hret_pc hr ▸ hlr_s0)
    (fun hr => hret_pc hr ▸ hother (s0.readReg64 .lr) hlr_ne_stub)
    hnoex_sf hnhalt_sf

/-- **Subroutine `Returned` specialization of `steps_transfer_memcpyGhostHookNarrow_On_ret`
    (`steps_transfer_memcpyGhostHookNarrow_On_returned`):**
    Transfers `Steps P_ghost s0 sf` to `Steps P_real s0 sf` for any subroutine outcome (`Returned`
    at `sf.pc = s0.readReg64 .lr`, `OutOfMemory`, `Signaled`, `Exited`, `Panicked`) given only
    `hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false` (no `s0.lr ≠ stubPc` premise needed
    because post-hook `Steps P_ghost (f u) sf` is used). -/
theorem steps_transfer_memcpyGhostHookNarrow_On_returned
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memcpyGhostHookBlk20 (keepMemcpyBlk20 mmpl) P_real mmpl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem) :
    Steps P_real s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem :=
  steps_transfer_memcpyGhostHookNarrow_On_ret
    hsvc_ghost hsvc_real hblk20_ext hghost_stub hother hreal_fr hreal_no hreal_stub_none
    hStub hInvLoaded hInvKf hsteps (fun hr => hret_pc hr ▸ hlr_s0) hnoex_sf hnhalt_sf hfr0 hinv0

/-- `f3RealProg617` specialization of `steps_transfer_memcpyGhostHookNarrow_On_returned`. -/
theorem steps_transfer_f3MemcpyGhostHookNarrow_On_returned
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc = some (f3MemcpyGhostHookNarrow mpl mmpl W))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (f3RealProg617 mpl mmpl W).externAt? pc)
    (hreal_fr : ∀ pc f, (f3RealProg617 mpl mmpl W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 20))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem) :
    Steps (f3RealProg617 mpl mmpl W) s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem :=
  steps_transfer_f3MemcpyGhostHookNarrow_On_ret
    hsvc_ghost hblk20_ext hghost_stub hother hreal_fr hreal_no hreal_stub_none
    hStub hInvLoaded hInvKf hsteps (fun hr => hret_pc hr ▸ hlr_s0) hnoex_sf hnhalt_sf hfr0 hinv0

/-! ## 4. `W`-Independent K-Convention `memcpy` Core (`P_real := emptyStdProg`) -/

/-- Plain `W`-independent K-convention `memcpy` ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyMemcpyGhostHook
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget
    (fun _ _ => masterMemcpySpec) hookMemcpy

/-- `K`-narrowed (`memcpySpecK keep masterMemcpySpec`) `W`-independent K-convention `memcpy`
    ghost hook. -/
@[expose] noncomputable def f3EmptyMemcpyGhostHookK
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget
    (fun _ _ => memcpySpecK keep masterMemcpySpec) hookMemcpy

theorem f3EmptyMemcpyGhostHook_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemcpyGhostHook keep P_sub entryTarget =
      memcpyGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    masterMemcpySpec hookMemcpy

theorem f3EmptyMemcpyGhostHookK_eq
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyMemcpyGhostHookK keep P_sub entryTarget =
      memcpyGhostHookK keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget
    (memcpySpecK keep masterMemcpySpec) hookMemcpy

theorem f3EmptyMemcpyGhostHook_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemcpyGhostHook keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget _ hookMemcpy s0

theorem f3EmptyMemcpyGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyMemcpyGhostHookK keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget _ hookMemcpy s0

theorem f3EmptyMemcpyGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemcpyGhostHook keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget _ hookMemcpy

theorem f3EmptyMemcpyGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyMemcpyGhostHookK keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget _ hookMemcpy

theorem f3EmptyMemcpyGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg,
      (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rw [f3EmptyMemcpyGhostHookK_eq] at hnoex
  exact memcpyGhostHookK_keepLr_false_of_noException hnoex

/-- `W`-independent `StepsUntil emptyStdProg (SubroutineStop u)` first-stop execution witness for
    `f3EmptyMemcpyGhostHook`. -/
theorem f3EmptyMemcpyGhostHook_stepsUntil
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemcpyGhostHook keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemcpyGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hActPre : ActiveF3CallPre (fun _ _ => masterMemcpySpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyMemcpyGhostHook f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ := (activeF3CallPre_const_iff masterMemcpySpec u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS (P_real := emptyStdProg) rfl hsvc_sub (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterMemcpy_of_hasWords hsub_no hwords)
      (specStripSInvariant_masterMemcpy keep)
      specPreservesFsTrace_masterMemcpy
      masterMemcpy_pre_setPC
      masterMemcpy_outcome_setPC
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold f3EmptyMemcpyGhostHook f3LinkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1, hchoose.2.1, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-- `W`-independent `StepsUntil emptyStdProg (SubroutineStop u)` first-stop execution witness for
    `f3EmptyMemcpyGhostHookK` (auto-discharging `keep (u.readReg64 .lr) = false` from `hnoex`). -/
theorem f3EmptyMemcpyGhostHookK_stepsUntil
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    {u : State}
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget)
        (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u) ∧
      SubroutineStop u (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  classical
  have hlr_out : keep (u.readReg64 .lr) = false :=
    f3EmptyMemcpyGhostHookK_keepLr_false_of_noException hnoex
  have hActPre : ActiveF3CallPre (fun _ _ => memcpySpecK keep masterMemcpySpec) u := by
    by_contra hnAct
    apply hnoex "ghost-hook precondition violated"
    unfold f3EmptyMemcpyGhostHookK f3LinkedCallHook
    simp [hnAct]
  obtain ⟨_, hsp, x, R, hpre⟩ :=
    (activeF3CallPre_const_iff (memcpySpecK keep masterMemcpySpec) u).mp hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS (P_real := emptyStdProg) rfl hsvc_sub (fun _ _ => rfl) hsub_no
      (subroutine_ok_masterMemcpyK_of_hasWords keep hsub_no hwords)
      (specStripSInvariant_masterMemcpyK keep)
      (specPreservesFsTrace_masterMemcpyK keep)
      (masterMemcpyK_pre_setPC keep)
      (masterMemcpyK_outcome_setPC keep)
      hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep emptyStdProg P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold f3EmptyMemcpyGhostHookK f3LinkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1, hchoose.2.1, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-- Memory-guarded `emptyStdProg → P_real` replay for `f3EmptyMemcpyGhostHook`. -/
theorem f3EmptyMemcpyGhostHook_replayOn_of_emptyLift
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (f3EmptyMemcpyGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyMemcpyGhostHook keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨huntil, hstop, hfr_sf, hfs_sf⟩ :=
    f3EmptyMemcpyGhostHook_stepsUntil hsvc_sub hsub_no hwords hrun hnoex hfr hlr
      (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (f3EmptyMemcpyGhostHook keep P_sub entryTarget u) :=
    hLift u _ hrun hfr hinv huntil hstop
  have hSteps : Steps P_real u (f3EmptyMemcpyGhostHook keep P_sub entryTarget u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Memory-guarded `emptyStdProg → P_real` replay for `f3EmptyMemcpyGhostHookK` (zero caller `lr`
    hypothesis). -/
theorem f3EmptyMemcpyGhostHookK_replayOn_of_emptyLift
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State), u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf → Steps P_real (u.setPC entryTarget) sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨huntil, hstop, hfr_sf, hfs_sf⟩ :=
    f3EmptyMemcpyGhostHookK_stepsUntil hsvc_sub hsub_no hwords hrun hnoex hfr
      (hInvLoaded u.mem hfr hinv)
  have hSteps : Steps P_real u (f3EmptyMemcpyGhostHookK keep P_sub entryTarget u) :=
    (hStub u hpc hrun hfr hinv).trans (hLift u _ hrun hfr hinv huntil hstop)
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Single-row `GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real` for
    `f3EmptyMemcpyGhostHook`. -/
theorem f3EmptyMemcpyGhostHook_replaysS_of_emptyLift
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemcpyGhostHook keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemcpyGhostHook_replayOn_of_emptyLift
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLift
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hlr hinv
      ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real` for
    `f3EmptyMemcpyGhostHookK` (polymorphic in `keep_any`). -/
theorem f3EmptyMemcpyGhostHookK_replaysS_of_emptyLift
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemcpyGhostHookK keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hLift : ∀ (u sf : State),
      u.status = .Running →
      ExecFrozen u.mem →
      InvMem u.mem →
      StepsUntil emptyStdProg (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := f3EmptyMemcpyGhostHookK_replayOn_of_emptyLift
    hsvc_sub hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf hLift
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn
