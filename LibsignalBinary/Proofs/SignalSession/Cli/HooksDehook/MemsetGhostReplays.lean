/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import

/-!
# Concrete `blk21` / `F3` Specializations & `GhostExternReplays` (`HooksDehook.MemsetGhostReplays`)

Design-independent Step 4 + concrete `mallocngBlockProg mmpl 21` and `F3` (`cliProgExtPlacedAt`)
specializations for `memsetGhostHook` and `memsetGhostHookK`:

1. **Concrete `P_sub` (`mallocngBlockProg mmpl 21 Syscall.standard` & `pureWordsProg`) specializations**:
   Discharges `hsvc_sub`, `hsub_no`, and `hwords`, and provides `f3MemsetGhostHook` /
   `f3MemsetGhostHookK` specialized to `P_real = cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
   (which additionally discharges `hsvc_real : P_real.svc = Syscall.standard` by `rfl`).
2. **`CodeLoaded` lifting into `stripExecOutside keep m`**:
   `codeLoaded_stripExecOutside_blk21` and `codeLoaded_stripExecOutside_pure21` under
   `KeepCoversBlk21 keep mmpl` (satisfied by `hole2_keepSub` via `keepCoversBlk21_of_range`,
   `keepMemsetBlk21 mmpl` via `keepCoversBlk21_keepMemsetBlk21`, or any `InRegion`-covering `keep`
   via `keepCoversBlk21_of_inRegion`).
3. **`GhostExternReplays` instantiations**:
   Instantiates `ghostExternReplays_of_linkedCallHook` (`AllocGhostLinkTransfer.lean:3037`) for
   `memsetGhostHook`, `memsetGhostHookK`, `memsetGhostHookBlk21`, `memsetGhostHookBlk21K`,
   `f3MemsetGhostHook`, and `f3MemsetGhostHookK`, with `keep (u.readReg64 .lr) = false` stated
   explicitly as a hypothesis per Amendment (c).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  StubReachesTarget ghostExternReplays_of_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  masterMemsetSpec memsetSpecK
  mallocngLib_blockLib21_text mallocng_blk21_code_length
  mallocngBlockProg21_hasWords mallocngBlockProg21_externAt_none
  subroutine_ok_masterMemset_of_hasWords subroutine_ok_masterMemsetK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  memsetGhostHook memsetGhostHookK memsetGhostHookBlk21 memsetGhostHookBlk21K
  keepMemsetBlk21 keepMallocng KeepCoversBlk21
  keepCoversBlk21_keepMemsetBlk21 keepCoversBlk21_of_inRegion keepCoversBlk21_of_range
  specStripSInvariant_masterMemset specStripSInvariant_masterMemsetK
  specPreservesFsTrace_masterMemset specPreservesFsTrace_masterMemsetK
  masterMemset_pre_setPC masterMemsetK_pre_setPC
  masterMemset_outcome_setPC masterMemsetK_outcome_setPC
  memsetGhostHook_master_ok memsetGhostHookK_masterK_ok
  memsetGhostHook_vmPreserved memsetGhostHookK_vmPreserved
)

/-! ## 1. Concrete `mallocngBlockProg mmpl 21` & `F3` (`cliProgExtPlacedAt`) Specializations -/

theorem mallocngBlockProg21_svc_eq (mmpl : Obj.MultiPlacement) :
    (mallocngBlockProg mmpl 21 Syscall.standard).svc = Syscall.standard := rfl

theorem pureWordsProg21_svc_eq (mmpl : Obj.MultiPlacement) :
    (pureWordsProg (mmpl.base 21) memsetWordsSym).svc = Syscall.standard := rfl

/-- Default-target abbreviation for the real Block-`617` CLI program
    `libsignalSessionLib.blockProgram mpl 617 (cliExternsPlaced mmpl W)` (definitionally `rfl`-equal
    to `F3HarnessPlaced.cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` without importing
    `CliElfLib`). -/
noncomputable abbrev f3RealProg617 (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl 617 (cliExternsPlaced mmpl W)

theorem f3RealProg617_svc_eq (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (f3RealProg617 mpl mmpl W).svc = Syscall.standard := rfl

/-- F3-specialized plain ghost `memset` hook at `P_real = f3RealProg617 mpl mmpl W`
    (`= cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`) and
    `P_sub = mallocngBlockProg mmpl 21 Syscall.standard` (`entryTarget = mmpl.base 21`),
    parametric in `keep : BitVec 64 → Bool`. -/
noncomputable abbrev f3MemsetGhostHook
    (keep : BitVec 64 → Bool) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  memsetGhostHookBlk21 keep (f3RealProg617 mpl mmpl W) mmpl

/-- F3-specialized `K`-narrowed ghost `memset` hook at `P_real = f3RealProg617 mpl mmpl W`
    (`= cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`) and
    `P_sub = mallocngBlockProg mmpl 21 Syscall.standard` (`entryTarget = mmpl.base 21`),
    parametric in `keep : BitVec 64 → Bool` (e.g. `keep := hole2_keepSub`). -/
noncomputable abbrev f3MemsetGhostHookK
    (keep : BitVec 64 → Bool) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  memsetGhostHookBlk21K keep (f3RealProg617 mpl mmpl W) mmpl

/-- Concrete `masterMemsetSpec` `HookOk` for `memsetGhostHookBlk21` (all `P_sub` hypotheses
    discharged). -/
theorem memsetGhostHookBlk21_master_ok
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (memsetGhostHookBlk21 keep P_real mmpl) masterMemsetSpec :=
  memsetGhostHook_master_ok hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

/-- Concrete `memsetSpecK keep masterMemsetSpec` `HookOk` for `memsetGhostHookBlk21K` (all `P_sub`
    hypotheses discharged). -/
theorem memsetGhostHookBlk21K_masterK_ok
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (memsetGhostHookBlk21K keep P_real mmpl)
      (memsetSpecK keep masterMemsetSpec) :=
  memsetGhostHookK_masterK_ok hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)

theorem memsetGhostHookBlk21_vmPreserved
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (s0 : State) :
    VmPreserved s0 (memsetGhostHookBlk21 keep P_real mmpl s0) :=
  memsetGhostHook_vmPreserved hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) s0

theorem memsetGhostHookBlk21K_vmPreserved
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (s0 : State) :
    VmPreserved s0 (memsetGhostHookBlk21K keep P_real mmpl s0) :=
  memsetGhostHookK_vmPreserved hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard) s0

/-- Concrete `masterMemsetSpec` `HookOk` for `f3MemsetGhostHook` (only `hreal_no` remains). -/
theorem f3MemsetGhostHook_master_ok
    {keep : BitVec 64 → Bool} (mpl mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none) :
    HookOk (f3MemsetGhostHook keep mpl mmpl W) masterMemsetSpec :=
  memsetGhostHookBlk21_master_ok mmpl (f3RealProg617_svc_eq mpl mmpl W) hreal_no

/-- Concrete `memsetSpecK keep masterMemsetSpec` `HookOk` for `f3MemsetGhostHookK`
    (only `hreal_no` remains). -/
theorem f3MemsetGhostHookK_masterK_ok
    {keep : BitVec 64 → Bool} (mpl mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none) :
    HookOk (f3MemsetGhostHookK keep mpl mmpl W) (memsetSpecK keep masterMemsetSpec) :=
  memsetGhostHookBlk21K_masterK_ok mmpl (f3RealProg617_svc_eq mpl mmpl W) hreal_no

/-! ## 2. `CodeLoaded` Lifting & `GhostExternReplays` Instantiations -/

private theorem blockProgram_code_eq (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (i : Nat)
    (externs overrides : String → Option (State → State)) (svc : State → State) :
    (lib.blockProgram mpl i externs overrides svc).code =
      (lib.blockLib i).text.patched (lib.blockPlacement mpl i) := rfl

theorem mallocngBlockProg21_code_length (mmpl : Obj.MultiPlacement) (svc : State → State) :
    (mallocngBlockProg mmpl 21 svc).code.length = 260 := by
  have hcode : (mallocngBlockProg mmpl 21 svc).code =
      (mallocngLib.blockLib 21).text.patched (mallocngLib.blockPlacement mmpl 21) :=
    blockProgram_code_eq mallocngLib mmpl 21 _ _ svc
  rw [hcode, Obj.CodeBlock.length_patched, mallocngLib_blockLib21_text, mallocng_blk21_code_length]

/-- Lift `prog.CodeLoaded m` into `stripExecOutside keep m` whenever `keep` covers `prog`'s code
    bytes. -/
theorem codeLoaded_stripExecOutside_of_keep
    {keep : BitVec 64 → Bool} {prog : Program} {m : Memory}
    (hkeep : ∀ off : Nat, off < prog.code.length → keep (prog.base + BitVec.ofNat 64 off) = true)
    (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun off hoff => ?_
  have hk : keep (prog.base + BitVec.ofNat 64 off) = true := hkeep off hoff
  refine ⟨?_, ?_, ?_⟩
  · rw [strip_read8]
    exact hL.byte_eq off hoff
  · rw [strip_perm, hk, hL.perm_eq off hoff]
    rfl
  · rw [strip_isLazyFree]
    exact hL.isLazyFree_eq off hoff

/-- Lift `(mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m` into `stripExecOutside keep m`
    whenever `KeepCoversBlk21 keep mmpl` holds (e.g. `keep = hole2_keepSub` or `keepMallocng mmpl`). -/
theorem codeLoaded_stripExecOutside_blk21
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} {m : Memory}
    (hkeep : KeepCoversBlk21 keep mmpl)
    (hL : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded (stripExecOutside keep m) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  rw [mallocngBlockProg21_code_length] at hoff
  exact hkeep off hoff

/-- Lift `(pureWordsProg (mmpl.base 21) memsetWordsSym).CodeLoaded m` into `stripExecOutside keep m`
    whenever `KeepCoversBlk21 keep mmpl` holds. -/
theorem codeLoaded_stripExecOutside_pure21
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} {m : Memory}
    (hkeep : KeepCoversBlk21 keep mmpl)
    (hL : (pureWordsProg (mmpl.base 21) memsetWordsSym).CodeLoaded m) :
    (pureWordsProg (mmpl.base 21) memsetWordsSym).CodeLoaded (stripExecOutside keep m) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  change off < (Program.ofWords 0#64 memsetWordsSym).code.length at hoff
  have hlen : (Program.ofWords 0#64 memsetWordsSym).code.length = 260 := by decide +kernel
  exact hkeep off (by omega)

/-- **`GhostExternReplays` arm for `memsetGhostHook` (generic `P_sub`)**:
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_memsetGhostHook` (takes
    unguarded `StubReachesTarget`, which is vacuous when `stubPc ≠ entryTarget`; do not use for the
    CLI cutover).*
    Instantiates `ghostExternReplays_of_linkedCallHook` with `keep (u.readReg64 .lr) = false` as an
    explicit hypothesis. All spec-invariance and `P_sub` verification obligations (`hOk`,
    `hSpecInv`, `hFsT`, `hPrePC`, `hOutPC`) are discharged. -/
theorem ghostExternReplays_memsetGhostHook
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hInvCode : ∀ m : Memory, ExecFrozen m → Inv m → P_sub.CodeLoaded (stripExecOutside keep m)) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHook keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u (memsetGhostHook keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memsetGhostHook keep P_real P_sub entryTarget u).mem :=
  ghostExternReplays_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvCode
    (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemset keep)
    specPreservesFsTrace_masterMemset
    masterMemset_pre_setPC
    masterMemset_outcome_setPC

/-- **`GhostExternReplays` arm for `memsetGhostHookK` (generic `P_sub`, `K`-route)**:
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_memsetGhostHookK_autoLr`
    (takes unguarded `StubReachesTarget`; do not use for the CLI cutover).*
    States `keep (u.readReg64 .lr) = false` explicitly per Amendment (c) (and note
    `memsetGhostHookK_keepLr_false_of_noException` also derives `keep (u.readReg64 .lr) = false`
    directly from `hnoex`!). -/
theorem ghostExternReplays_memsetGhostHookK
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hInvCode : ∀ m : Memory, ExecFrozen m → Inv m → P_sub.CodeLoaded (stripExecOutside keep m)) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u (memsetGhostHookK keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memsetGhostHookK keep P_real P_sub entryTarget u).mem :=
  ghostExternReplays_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvCode
    (subroutine_ok_masterMemsetK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemsetK keep)
    (specPreservesFsTrace_masterMemsetK keep)
    (masterMemsetK_pre_setPC keep)
    (masterMemsetK_outcome_setPC keep)

/-- **`GhostExternReplays` arm for `memsetGhostHookBlk21` (`P_sub = mallocngBlockProg mmpl 21`)**:
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_memsetGhostHookBlk21`
    (takes unguarded `StubReachesTarget`; do not use for the CLI cutover).*
    Discharges `hsvc_sub`, `hsub_no`, `hwords`, and reduces `hInvCode` to `KeepCoversBlk21 keep mmpl`
    + `(mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m` under `Inv m`. -/
theorem ghostExternReplays_memsetGhostHookBlk21
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc (mmpl.base 21))
    (hkeep : KeepCoversBlk21 keep mmpl)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookBlk21 keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u (memsetGhostHookBlk21 keep P_real mmpl u) ∧
      ExecFrozen (memsetGhostHookBlk21 keep P_real mmpl u).mem :=
  ghostExternReplays_memsetGhostHook
    hsvc_real
    (mallocngBlockProg21_svc_eq mmpl)
    hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)
    hreal_stub_none
    hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk21 hkeep (hInvLoaded m hfr hinv))

/-- **`GhostExternReplays` arm for `memsetGhostHookBlk21K` (`P_sub = mallocngBlockProg mmpl 21`,
    `K`-route)**:
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_memsetGhostHookBlk21K_autoLr`
    (takes unguarded `StubReachesTarget`; do not use for the CLI cutover).*
    Discharges `hsvc_sub`, `hsub_no`, `hwords`, and reduces `hInvCode` to `KeepCoversBlk21 keep mmpl`
    + `(mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m` under `Inv m`. -/
theorem ghostExternReplays_memsetGhostHookBlk21K
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc (mmpl.base 21))
    (hkeep : KeepCoversBlk21 keep mmpl)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookBlk21K keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u (memsetGhostHookBlk21K keep P_real mmpl u) ∧
      ExecFrozen (memsetGhostHookBlk21K keep P_real mmpl u).mem :=
  ghostExternReplays_memsetGhostHookK
    hsvc_real
    (mallocngBlockProg21_svc_eq mmpl)
    hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)
    hreal_stub_none
    hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk21 hkeep (hInvLoaded m hfr hinv))

/-- **`GhostExternReplays` arm for `f3MemsetGhostHook` (`P_real = f3RealProg617 mpl mmpl W`)**:
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHook` and
    `W`-independent `SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset` (do not use for the cutover).*
    Additionally discharges `hsvc_real` (`rfl`). -/
theorem ghostExternReplays_f3MemsetGhostHook
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hkeep : KeepCoversBlk21 keep mmpl)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHook keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHook keep mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHook keep mpl mmpl W u).mem :=
  ghostExternReplays_memsetGhostHookBlk21
    (f3RealProg617_svc_eq mpl mmpl W)
    hreal_no hreal_stub_none hStub hkeep hInvLoaded

/-- **`GhostExternReplays` arm for `f3MemsetGhostHookK` (`P_real = f3RealProg617 mpl mmpl W`,
    `K`-route)**:
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookK_autoLr`
    and `SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookK_replaysS` (do not use
    for the cutover).*
    Additionally discharges `hsvc_real` (`rfl`). -/
theorem ghostExternReplays_f3MemsetGhostHookK
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hkeep : KeepCoversBlk21 keep mmpl)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookK keep mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookK keep mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookK keep mpl mmpl W u).mem :=
  ghostExternReplays_memsetGhostHookBlk21K
    (f3RealProg617_svc_eq mpl mmpl W)
    hreal_no hreal_stub_none hStub hkeep hInvLoaded

/-! ## 3. Concrete `keep` Instantiations (`hole2_keepSub` Range, `keepMallocng`, & Narrow `keepMemsetBlk21`) -/

/-- Monotonicity of `KeepCoversBlk21` under pointwise inclusion of `keep` predicates
    (e.g. lifting `keepMallocng mmpl` into `hole2_keepSub` via `hole2_keepSub_mallocng`). -/
theorem keepCoversBlk21_of_superset
    {keep1 keep2 : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement}
    (h1 : KeepCoversBlk21 keep1 mmpl)
    (hsub : ∀ a : BitVec 64, keep1 a = true → keep2 a = true) :
    KeepCoversBlk21 keep2 mmpl :=
  fun off hoff => hsub _ (h1 off hoff)

/-- `keepMallocng mmpl` (`(mallocngLib.findCodeBlock mmpl a).isSome`) covers `blk21` whenever
    `mallocngLib.Placeable mmpl` holds. -/
theorem keepCoversBlk21_keepMallocng
    {mmpl : Obj.MultiPlacement} (hpl : mallocngLib.Placeable mmpl) :
    KeepCoversBlk21 (keepMallocng mmpl) mmpl := by
  refine keepCoversBlk21_of_inRegion fun a hin => ?_
  unfold keepMallocng
  have hlen : (mallocngLib.blockPatched mmpl 21).length = 260 := by
    change ((mallocngLib.blockLib 21).text.patched (mallocngLib.blockPlacement mmpl 21)).length = 260
    rw [Obj.CodeBlock.length_patched, mallocngLib_blockLib21_text, mallocng_blk21_code_length]
  have hlt : 21 < mallocngLib.blocks.length := by decide
  rw [← hlen] at hin
  rw [findCodeBlock_eq_some_of_inRegion hpl hlt hin]
  rfl

/-- Address-free half-open interval `keep` predicate `decide (lo ≤ a.toNat ∧ a.toNat < hi)`.
    Definitionally (`rfl`) equal to `ElfSlicesPqOomPlacedInst.hole2_keepSub` when instantiated at
    `hole2_keepSub`'s `[lo, hi)` bounds, without importing `CliElfLib` or hardcoding hex addresses. -/
@[expose] def keepRange (lo hi : Nat) (a : BitVec 64) : Bool :=
  decide (lo ≤ a.toNat ∧ a.toNat < hi)

theorem keepCoversBlk21_keepRange
    {mmpl : Obj.MultiPlacement} (lo hi : Nat)
    (hlo : lo ≤ (mmpl.base 21).toNat)
    (hhi : (mmpl.base 21).toNat + 260 ≤ hi)
    (hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64) :
    KeepCoversBlk21 (keepRange lo hi) mmpl :=
  keepCoversBlk21_of_range lo hi
    (fun _ h1 h2 => decide_eq_true ⟨h1, h2⟩)
    hlo hhi hnowrap

/-- F3 ghost `memset` hook specialized to `keep = keepRange lo hi` (`rfl`-identical to
    `f3MemsetGhostHook hole2_keepSub mpl mmpl W` at `hole2_keepSub`'s `[lo, hi)` bounds). -/
noncomputable abbrev f3MemsetGhostHookRange
    (lo hi : Nat) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemsetGhostHook (keepRange lo hi) mpl mmpl W

/-- F3 `K`-narrowed ghost `memset` hook specialized to `keep = keepRange lo hi` (`rfl`-identical to
    `f3MemsetGhostHookK hole2_keepSub mpl mmpl W` at `hole2_keepSub`'s `[lo, hi)` bounds). -/
noncomputable abbrev f3MemsetGhostHookRangeK
    (lo hi : Nat) (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemsetGhostHookK (keepRange lo hi) mpl mmpl W

/-- F3 ghost `memset` hook specialized to narrow `keep = keepMemsetBlk21 mmpl` (`blk21`'s `260` B
    only, for 2-pass `P_ghost8 → P_A` transfer with `0` `LsRetAddr624` caller obligations). -/
noncomputable abbrev f3MemsetGhostHookNarrow
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemsetGhostHook (keepMemsetBlk21 mmpl) mpl mmpl W

/-- F3 `K`-narrowed ghost `memset` hook specialized to narrow `keep = keepMemsetBlk21 mmpl`. -/
noncomputable abbrev f3MemsetGhostHookNarrowK
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : State → State :=
  f3MemsetGhostHookK (keepMemsetBlk21 mmpl) mpl mmpl W

/-- `GhostExternReplays` for `f3MemsetGhostHookRange` (`hole2_keepSub` range instantiation).
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookRange`
    (do not use for the cutover).* -/
theorem ghostExternReplays_f3MemsetGhostHookRange
    {lo hi : Nat} {Inv : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hlo : lo ≤ (mmpl.base 21).toNat)
    (hhi : (mmpl.base 21).toNat + 260 ≤ hi)
    (hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64)
    (hreal_no : ∀ pc, keepRange lo hi pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookRange lo hi mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepRange lo hi (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookRange lo hi mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookRange lo hi mpl mmpl W u).mem :=
  ghostExternReplays_f3MemsetGhostHook
    hreal_no hreal_stub_none hStub
    (keepCoversBlk21_keepRange lo hi hlo hhi hnowrap)
    hInvLoaded

/-- `GhostExternReplays` for `f3MemsetGhostHookRangeK` (`hole2_keepSub` `K`-route instantiation).
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookRangeK_autoLr`
    and `SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookK_replaysS` (do not use
    for the cutover).* -/
theorem ghostExternReplays_f3MemsetGhostHookRangeK
    {lo hi : Nat} {Inv : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hlo : lo ≤ (mmpl.base 21).toNat)
    (hhi : (mmpl.base 21).toNat + 260 ≤ hi)
    (hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64)
    (hreal_no : ∀ pc, keepRange lo hi pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookRangeK lo hi mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepRange lo hi (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookRangeK lo hi mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookRangeK lo hi mpl mmpl W u).mem :=
  ghostExternReplays_f3MemsetGhostHookK
    hreal_no hreal_stub_none hStub
    (keepCoversBlk21_keepRange lo hi hlo hhi hnowrap)
    hInvLoaded

/-- `GhostExternReplays` for `f3MemsetGhostHookNarrow` (`keep = keepMemsetBlk21 mmpl`; `KeepCoversBlk21`
    discharged unconditionally).
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookNarrow`
    and `SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset.h2k_memsetGhostHookNarrow_stub_replayOn_cli617`
    (do not use for the cutover).* -/
theorem ghostExternReplays_f3MemsetGhostHookNarrow
    {Inv : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrow mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrow mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrow mpl mmpl W u).mem :=
  ghostExternReplays_f3MemsetGhostHook
    hreal_no hreal_stub_none hStub
    (keepCoversBlk21_keepMemsetBlk21 mmpl)
    hInvLoaded

/-- `GhostExternReplays` for `f3MemsetGhostHookNarrowK` (`keep = keepMemsetBlk21 mmpl`, `K`-route).
    *Superseded by `HooksDehook.MemsetGhostReplaysOn.ghostExternReplaysOn_f3MemsetGhostHookNarrowK_autoLr`
    (do not use for the cutover).* -/
theorem ghostExternReplays_f3MemsetGhostHookNarrowK
    {Inv : Memory → Prop}
    {mpl mmpl : Obj.MultiPlacement} {W : CliHooks} {stubPc : BitVec 64}
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none)
    (hreal_stub_none : (f3RealProg617 mpl mmpl W).externAt? stubPc = none)
    (hStub : StubReachesTarget (f3RealProg617 mpl mmpl W) stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → Inv m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m) :
    (f3RealProg617 mpl mmpl W).externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f3MemsetGhostHookNarrowK mpl mmpl W u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps (f3RealProg617 mpl mmpl W) u (f3MemsetGhostHookNarrowK mpl mmpl W u) ∧
      ExecFrozen (f3MemsetGhostHookNarrowK mpl mmpl W u).mem :=
  ghostExternReplays_f3MemsetGhostHookK
    hreal_no hreal_stub_none hStub
    (keepCoversBlk21_keepMemsetBlk21 mmpl)
    hInvLoaded

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays
