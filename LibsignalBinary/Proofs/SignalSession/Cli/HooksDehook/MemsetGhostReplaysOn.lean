/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet -- proof-setup: allow-public-import

/-!
# Memory-Guarded `On` / `S` Replays & `(A1)`+`(A2)` Trap Corollaries (`HooksDehook.MemsetGhostReplaysOn`)

Fixes the unguarded `StubReachesTarget` applicability gap (`rev_c1.md` §4a, `rev_c5.md` §4) across
all `memset` ghost hook variants and wires the generalized `(A1)`+`(A2)` closed-trap lemmas
(`HooksDehook.MemsetLrTrapRet`) into memory-guarded `On`/`S` replays and `Steps` transfer:

1. **Per-Stub Guarded `On` Replays (`StubReachesTargetOn InvMem`)**:
   Instantiates `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook` for `memsetGhostHook`,
   `memsetGhostHookK` (both explicit-`lr` and `noException`-auto-`lr`), `memsetGhostHookBlk21`,
   `memsetGhostHookBlk21K`, `f3MemsetGhostHook`, `f3MemsetGhostHookK`, `f3MemsetGhostHookNarrow`,
   `f3MemsetGhostHookRx`, and `f3MemsetGhostHookRxK`.
2. **Single-Row `GhostExternReplaysS` Packagers**:
   Trajectory-independent `GhostExternReplaysS` witnesses for `memsetGhostHook`,
   `memsetGhostHookK` (polymorphic in outer `keep_any`), and `f3MemsetGhostHookNarrow` (retaining
   `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` as the ghost-arm binder).
3. **Closed-Trap `_of_trap_ret` Guarded `On` Replays & `Steps` Transfer (`(A1)` + `(A2)`)**:
   Discharges `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` internally via
   `MemsetLrTrapRet.blk21_lr_trap_after_hook_ret` under:
   - `(A1)` `hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false`,
     `∀ msg, sf.status ≠ .Exception msg`, `sf.status ≠ .Halted` (covering `Exited`, `Panicked`,
     `OutOfMemory`, `Signaled`, and subroutine `Returned` when `keepMemsetBlk21 (s0.lr) = false`),
   - `(A2)` per-PC `Blk21TrapHook` existential `hblk21_ext` (supporting mixed ghost tables).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification.SignalSession (CliHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn steps_transfer_ghostOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook ghostExternReplaysOn_of_single_stub
  ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords
  subroutine_ok_masterMemset_of_hasWords subroutine_ok_masterMemsetK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  KeepCoversBlk21 keepCoversBlk21_keepMemsetBlk21 keepMemsetBlk21
  masterMemset_outcome_setPC masterMemset_pre_setPC
  masterMemsetK_outcome_setPC masterMemsetK_pre_setPC
  memsetGhostHook memsetGhostHookBlk21 memsetGhostHookBlk21K memsetGhostHookK
  memsetGhostHookK_keepLr_false_of_noException
  specPreservesFsTrace_masterMemset specPreservesFsTrace_masterMemsetK
  specStripSInvariant_masterMemset specStripSInvariant_masterMemsetK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  codeLoaded_stripExecOutside_blk21
  f3MemsetGhostHook f3MemsetGhostHookK f3MemsetGhostHookNarrow f3MemsetGhostHookNarrowK
  f3MemsetGhostHookRange f3MemsetGhostHookRangeK f3RealProg617 f3RealProg617_svc_eq
  keepCoversBlk21_keepRange keepRange mallocngBlockProg21_svc_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (
  Blk21TrapHook blk21TrapHook_memsetGhostHook_of_cover blk21_lr_trap_after_hook_ret
  blk21_lr_trap_false_ret
)

/-! ## 1. Per-Stub Memory-Guarded `On` Replays (`StubReachesTargetOn InvMem`) -/

/-- Generic memory-guarded `On` replay for plain `memsetGhostHook`. -/
theorem ghostExternReplaysOn_memsetGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
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
        (memsetGhostHook keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memsetGhostHook keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memsetGhostHook keep P_real P_sub entryTarget u).mem ∧
      InvMem (memsetGhostHook keep P_real P_sub entryTarget u).mem :=
  ghostExternReplaysOn_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemset keep)
    specPreservesFsTrace_masterMemset
    masterMemset_pre_setPC
    masterMemset_outcome_setPC

/-- Generic memory-guarded `On` replay for `K`-narrowed `memsetGhostHookK` (explicit `hlr`
    shape matching `GhostExternReplaysS`). -/
theorem ghostExternReplaysOn_memsetGhostHookK
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
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
        (memsetGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memsetGhostHookK keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memsetGhostHookK keep P_real P_sub entryTarget u).mem ∧
      InvMem (memsetGhostHookK keep P_real P_sub entryTarget u).mem :=
  ghostExternReplaysOn_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemsetK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemsetK keep)
    (specPreservesFsTrace_masterMemsetK keep)
    (masterMemsetK_pre_setPC keep)
    (masterMemsetK_outcome_setPC keep)

/-- Memory-guarded `On` replay for `memsetGhostHookK` with **zero caller `lr` premise**
    (`keep (u.readReg64 .lr) = false` discharged automatically from `hnoex`). -/
theorem ghostExternReplaysOn_memsetGhostHookK_autoLr
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
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
        (memsetGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memsetGhostHookK keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memsetGhostHookK keep P_real P_sub entryTarget u).mem ∧
      InvMem (memsetGhostHookK keep P_real P_sub entryTarget u).mem := by
  have hRep := ghostExternReplaysOn_memsetGhostHookK
    hsvc_real hsvc_sub hreal_no hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf
  exact ⟨hRep.1, fun u hpc hrun hnoex hfr hinv =>
    hRep.2 u hpc hrun hnoex hfr (memsetGhostHookK_keepLr_false_of_noException hnoex) hinv⟩

/-- `blk21`-specialized memory-guarded `On` replay for `memsetGhostHookBlk21` (lifts
    `(mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m` into `stripExecOutside keep m` via
    `KeepCoversBlk21 keep mmpl`, e.g. `F3CodeInv.mngBlockCodeLoaded` at `j = 21`). -/
theorem ghostExternReplaysOn_memsetGhostHookBlk21
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookBlk21 keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memsetGhostHookBlk21 keep P_real mmpl u) ∧
      ExecFrozen (memsetGhostHookBlk21 keep P_real mmpl u).mem ∧
      InvMem (memsetGhostHookBlk21 keep P_real mmpl u).mem :=
  ghostExternReplaysOn_memsetGhostHook
    hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)
    hreal_stub_none hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk21 hcover (hInvLoaded m hfr hinv))
    hInvKf

/-- `blk21`-specialized memory-guarded `On` replay for `memsetGhostHookBlk21K` (explicit `hlr`). -/
theorem ghostExternReplaysOn_memsetGhostHookBlk21K
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookBlk21K keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memsetGhostHookBlk21K keep P_real mmpl u) ∧
      ExecFrozen (memsetGhostHookBlk21K keep P_real mmpl u).mem ∧
      InvMem (memsetGhostHookBlk21K keep P_real mmpl u).mem :=
  ghostExternReplaysOn_memsetGhostHookK
    hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)
    hreal_stub_none hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk21 hcover (hInvLoaded m hfr hinv))
    hInvKf

/-- `blk21`-specialized memory-guarded `On` replay for `memsetGhostHookBlk21K` (auto-`lr`). -/
theorem ghostExternReplaysOn_memsetGhostHookBlk21K_autoLr
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookBlk21K keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (memsetGhostHookBlk21K keep P_real mmpl u) ∧
      ExecFrozen (memsetGhostHookBlk21K keep P_real mmpl u).mem ∧
      InvMem (memsetGhostHookBlk21K keep P_real mmpl u).mem := by
  have hRep := ghostExternReplaysOn_memsetGhostHookBlk21K
    hsvc_real hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf
  exact ⟨hRep.1, fun u hpc hrun hnoex hfr hinv =>
    hRep.2 u hpc hrun hnoex hfr (memsetGhostHookK_keepLr_false_of_noException hnoex) hinv⟩

/-- Guarded `On` replay for `f3MemsetGhostHook` (`P_real := f3RealProg617 mpl mmpl W`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {mpl mmpl : Obj.MultiPlacement}
    {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHook keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHook keep mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHook keep mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHook keep mpl mmpl W u).mem :=
  ghostExternReplaysOn_memsetGhostHookBlk21
    (f3RealProg617_svc_eq mpl mmpl W) hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemsetGhostHookK` (explicit `hlr`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHookK
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {mpl mmpl : Obj.MultiPlacement}
    {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookK keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookK keep mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookK keep mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookK keep mpl mmpl W u).mem :=
  ghostExternReplaysOn_memsetGhostHookBlk21K
    (f3RealProg617_svc_eq mpl mmpl W) hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemsetGhostHookK` (auto-`lr`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHookK_autoLr
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {mpl mmpl : Obj.MultiPlacement}
    {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookK keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookK keep mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookK keep mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookK keep mpl mmpl W u).mem :=
  ghostExternReplaysOn_memsetGhostHookBlk21K_autoLr
    (f3RealProg617_svc_eq mpl mmpl W) hreal_no hcover hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemsetGhostHookNarrow` (`keep := keepMemsetBlk21 mmpl`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHookNarrow
    {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrow mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookNarrow mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemsetGhostHook
    hreal_no (keepCoversBlk21_keepMemsetBlk21 mmpl) hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemsetGhostHookNarrowK` (auto-`lr`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHookNarrowK_autoLr
    {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrowK mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrowK mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrowK mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookNarrowK mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemsetGhostHookK_autoLr
    hreal_no (keepCoversBlk21_keepMemsetBlk21 mmpl) hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemsetGhostHookRange` (`keep := keepRange lo hi`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHookRange
    {lo hi : Nat} {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hlo : lo ≤ (mmpl.base 21).toNat)
    (hhi : (mmpl.base 21).toNat + 260 ≤ hi)
    (hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64)
    (hreal_no : ∀ pc, keepRange lo hi pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookRange lo hi mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepRange lo hi (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookRange lo hi mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookRange lo hi mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookRange lo hi mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemsetGhostHook
    hreal_no (keepCoversBlk21_keepRange lo hi hlo hhi hnowrap)
    hreal_stub_none hStub hInvLoaded hInvKf

/-- Guarded `On` replay for `f3MemsetGhostHookRangeK` (auto-`lr`). -/
theorem ghostExternReplaysOn_f3MemsetGhostHookRangeK_autoLr
    {lo hi : Nat} {InvMem : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hlo : lo ≤ (mmpl.base 21).toNat)
    (hhi : (mmpl.base 21).toNat + 260 ≤ hi)
    (hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64)
    (hreal_no : ∀ pc, keepRange lo hi pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookRangeK lo hi mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookRangeK lo hi mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookRangeK lo hi mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookRangeK lo hi mpl mmpl W u).mem :=
  ghostExternReplaysOn_f3MemsetGhostHookK_autoLr
    hreal_no (keepCoversBlk21_keepRange lo hi hlo hhi hnowrap)
    hreal_stub_none hStub hInvLoaded hInvKf

/-! ## 2. Single-Row `GhostExternReplaysS` Packagers -/

/-- Single-row `GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real` for plain
    `memsetGhostHook` (`keep (u.readReg64 .lr) = false` retained as the ghost-arm binder). -/
theorem ghostExternReplaysS_memsetGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHook keep P_real P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real :=
  ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    (ghostExternReplaysOn_memsetGhostHook
      hsvc_real hsvc_sub hreal_no hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf)

/-- Single-row `GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real` for
    `memsetGhostHookK` (polymorphic in `keep_any` because `keep (u.readReg64 .lr) = false` is
    discharged internally from `hnoex`). -/
theorem ghostExternReplaysS_memsetGhostHookK
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHookK keep P_real P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := ghostExternReplaysOn_memsetGhostHookK_autoLr
    hsvc_real hsvc_sub hreal_no hsub_no hwords hreal_stub_none hStub hInvLoaded hInvKf
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv => hRep.2 u hpc hrun hnoex hfr hinv⟩

/-- Single-row `GhostExternReplaysS (keepMemsetBlk21 mmpl) (fun u => InvMem u.mem)` for
    `f3MemsetGhostHookNarrow` over `f3RealProg617 mpl mmpl W`. -/
theorem ghostExternReplaysS_f3MemsetGhostHookNarrow
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hghost_stub : P_ghost.externAt? stubPc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (f3RealProg617 mpl mmpl W).externAt? pc)
    (hreal_fr : ∀ pc f, (f3RealProg617 mpl mmpl W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS (keepMemsetBlk21 mmpl) (fun u => InvMem u.mem) P_ghost
      (f3RealProg617 mpl mmpl W) :=
  ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    (ghostExternReplaysOn_f3MemsetGhostHookNarrow
      hreal_no hreal_stub_none hStub hInvLoaded hInvKf)

/-! ## 3. `(A1)` + `(A2)` Closed-Trap `_of_trap` Guarded `On` Replays & `Steps` Transfer -/

/-- **Per-stub `(A1)` + `(A2)` trap-discharged guarded `On` replay
    (`ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret`):**
    Parametric in `P_ghost` and `P_real` (applicable both to Pass 1 `P_ghost8 → P_A` of a 2-pass
    cutover and to mixed passes), discharging `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`
    internally from `Steps P_ghost (f_ms u) sf` via `blk21_lr_trap_after_hook_ret` under `(A1)`
    (`hrun_sf'`, `hnoex_sf`, `hnhalt_sf`) and `(A2)` (`hblk21_ext`). -/
theorem ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let f_ms := memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) P_real mmpl
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f_ms u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f_ms u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f_ms u).mem →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f_ms u) ∧ ExecFrozen (f_ms u).mem ∧ InvMem (f_ms u).mem := by
  have hRep := ghostExternReplaysOn_memsetGhostHookBlk21
    hsvc_real hreal_no (keepCoversBlk21_keepMemsetBlk21 mmpl)
    hreal_stub_none hStub hInvLoaded hInvKf
  refine ⟨hRep.1, fun u hrest hpc hrun hnoex hkf hfr hinv => ?_⟩
  have hlr_false : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
    blk21_lr_trap_after_hook_ret
      (blk21TrapHook_memsetGhostHook_of_cover (fun _ h => h) P_real
        (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21))
      hblk21_ext
      ((hInvLoaded u.mem hfr hinv).of_keepsFrozen hkf)
      hrest hrun hrun_sf' hnoex_sf hnhalt_sf
  exact hRep.2 u hpc hrun hnoex hfr hlr_false hinv

/-- **`f3RealProg617` specialization (`ghostExternReplaysOn_f3MemsetGhostHookNarrow_of_trap_ret`):**
    Guarded `On` replacement for `MemsetLrTrap.ghostExternReplays_f3MemsetGhostHookNarrow_of_trap_gen`,
    based on `(A1)` + `(A2)` rather than `Exited ∨ Panicked` or unguarded `StubReachesTarget`. -/
theorem ghostExternReplaysOn_f3MemsetGhostHookNarrow_of_trap_ret
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f3MemsetGhostHookNarrow mpl mmpl W u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f3MemsetGhostHookNarrow mpl mmpl W u).mem →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrow mpl mmpl W u).mem ∧
      InvMem (f3MemsetGhostHookNarrow mpl mmpl W u).mem :=
  ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
    hblk21_ext (f3RealProg617_svc_eq mpl mmpl W) hreal_no hreal_stub_none hStub hInvLoaded hInvKf
    hrun_sf' hnoex_sf hnhalt_sf

/-- **Single-stub `GhostExternReplaysOn` from `(A1)` + `(A2)` (`keep_any`-polymorphic):**
    Produces a full `GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf`
    for **any** `keep_any : BitVec 64 → Bool` (including `fun _ => false`, where `hlr_calls` in
    `steps_transfer_ghostOn` is `rfl`) under `(A1)` + `(A2)`. -/
theorem ghostExternReplaysOn_single_memsetGhostHookNarrow_of_trap_ret
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    {s0 sf : State}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) P_real mmpl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have hRep := ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
    hblk21_ext hsvc_real hreal_no hreal_stub_none hStub hInvLoaded hInvKf
    hrun_sf' hnoex_sf hnhalt_sf
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother
    (fun pc f hr u _ _ _ hrun _ hkf hfr hinv =>
      ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u _ hrest hpc hrun hnoex hkf hfr _ hinv =>
      hRep.2 u hrest hpc hrun hnoex hkf hfr hinv⟩

/-- **End-to-End Pass-1 / Single-Stub Guarded `Steps` Cutover (`steps_transfer_memsetGhostHookNarrow_On_ret`):**
    Guarded `StubReachesTargetOn InvMem` + `(A1)` + `(A2)` replacement for
    `MemsetLrTrap.steps_transfer_f3MemsetGhostHookNarrow`, requiring **only** `hrun_sf'`, `hnoex_sf`,
    `hnhalt_sf` on `sf` and **zero** `lr` premise.
    *Applicability note (`rev_c6` F2):* `hother` requires a single ghost/real mismatch (`stubPc`)
    and `hghost_stub` ties the hook's `P_real` to the transfer's `P_real` (so instantiating `P_real`
    at `f3RealProg617 mpl mmpl W` is `W`-dependent and covers a `memset`-only pass, not the 8-row
    `W`-independent K CLI pass). The CLI route goes through
    `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617` (or
    `h2k_memsetGhostHookK_replaysS`) inside K's per-PC `GhostExternReplaysOn`. -/
theorem steps_transfer_memsetGhostHookNarrow_On_ret
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) P_real mmpl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
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
    ghostExternReplaysOn_single_memsetGhostHookNarrow_of_trap_ret (fun _ => false)
      hblk21_ext hghost_stub hother hreal_fr hsvc_real hreal_no hreal_stub_none
      hStub hInvLoaded hInvKf hrun_sf' hnoex_sf hnhalt_sf
  exact steps_transfer_ghostOn hsvc_ghost hsvc_real hno_new_hooks hsteps hnoex_sf hnhalt_sf
    hfr0 hinv0 hReplays
    (fun z _ _ _ _ _ _ _ hkf _ hinv => hInvKf z.mem _ hinv hkf)
    (fun z _ _ _ _ _ hkf _ hinv => hInvKf z.mem _ hinv hkf)
    (fun _ _ _ _ _ => rfl)

/-- `f3RealProg617` specialization of `steps_transfer_memsetGhostHookNarrow_On_ret`.
    *Applicability note (`rev_c6` F2):* Single-stub (`memset`-only pass) and `W`-dependent (`P_real =
    f3RealProg617 mpl mmpl W`); for the `W`-independent 8-row CLI K pass, use
    `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617` inside K's per-PC
    replay. -/
theorem steps_transfer_f3MemsetGhostHookNarrow_On_ret
    {InvMem : Memory → Prop}
    {P_ghost : Program} {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc = some (f3MemsetGhostHookNarrow mpl mmpl W))
    (hother : ∀ pc, pc ≠ stubPc →
      P_ghost.externAt? pc = (f3RealProg617 mpl mmpl W).externAt? pc)
    (hreal_fr : ∀ pc f, (f3RealProg617 mpl mmpl W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem) :
    Steps (f3RealProg617 mpl mmpl W) s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem :=
  steps_transfer_memsetGhostHookNarrow_On_ret
    hsvc_ghost (f3RealProg617_svc_eq mpl mmpl W) hblk21_ext hghost_stub hother hreal_fr
    hreal_no hreal_stub_none hStub hInvLoaded hInvKf hsteps hrun_sf' hnoex_sf hnhalt_sf hfr0 hinv0

/-- **Subroutine `Returned` specialization of `(A1)` + `(A2)` `hlr_calls` (`blk21_lr_trap_false_returned`):**
    When `sf` is either non-`.Running` (OOM / Signaled / Exited / Panicked) or `.Running` at the
    subroutine's caller return address `sf.pc = s0.readReg64 .lr` (`SubroutineStop s0 sf`),
    `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false` and `s0.readReg64 .lr ≠ stubPc` (for single-stub
    `P_ghost` vs `P_real`, or more generally `P_ghost.externAt? (s0.readReg64 .lr) =
    P_real.externAt? (s0.readReg64 .lr)`) discharge both `hrun_sf'` and `hret_no_mis`. -/
theorem blk21_lr_trap_false_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hlr_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false)
    (hlr_ne_stub : s0.readReg64 .lr ≠ stubPc)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
  blk21_lr_trap_false_ret hblk21_ext hmis_trap hc_codeLoaded
    (fun hr => hret_pc hr ▸ hlr_s0)
    (fun hr => hret_pc hr ▸ hother (s0.readReg64 .lr) hlr_ne_stub)
    hnoex_sf hnhalt_sf

/-- **Subroutine `Returned` specialization of `steps_transfer_memsetGhostHookNarrow_On_ret`:**
    Transfers `Steps P_ghost s0 sf` to `Steps P_real s0 sf` for any subroutine outcome (`Returned`
    at `sf.pc = s0.readReg64 .lr`, `OutOfMemory`, `Signaled`, `Exited`, `Panicked`) given only
    `hlr_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false` (not even needing `s0.lr ≠ stubPc`
    because `steps_transfer_memsetGhostHookNarrow_On_ret` uses post-hook `Steps P_ghost (f u) sf`).
    *Applicability note (`rev_c6` F2):* Single-stub (`memset`-only pass) and ties the hook's `P_real`
    to the transfer's `P_real` (`W`-dependent at `f3RealProg617`); for the `W`-independent 8-row CLI
    K pass, use `ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617` (or
    `h2k_memsetGhostHookK_replaysS`) inside K's per-PC `GhostExternReplaysOn`. -/
theorem steps_transfer_memsetGhostHookNarrow_On_returned
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hghost_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) P_real mmpl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hlr_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem) :
    Steps P_real s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem :=
  steps_transfer_memsetGhostHookNarrow_On_ret
    hsvc_ghost hsvc_real hblk21_ext hghost_stub hother hreal_fr hreal_no hreal_stub_none
    hStub hInvLoaded hInvKf hsteps (fun hr => hret_pc hr ▸ hlr_s0) hnoex_sf hnhalt_sf hfr0 hinv0

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
