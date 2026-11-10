/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import ProofLib.Process.OracleEq

/-!
# Ghost `memcpy` Hook & Complete `HookOk` Suite (`HooksDehook.MemcpyGhost`)

Design-independent Steps 2–3 for de-hooking `memcpy` (`VerifiedLibraries.mallocngLib` block 20,
`396` bytes = `99` words) using `linkedCallHook` (`AllocGhostLinkTransfer.lean`):

1. **Ghost `memcpy` hooks (`memcpyGhostHook`, `memcpyGhostHookK`)**:
   - `memcpyGhostHook keep P_real P_sub entryTarget`: wraps `masterMemcpySpec` (indexed by
     `ro : Bool`, covering both `src ↦ₛ bs` and `src ↦ᵣ bs`) with fallback `hookMemcpy`.
     Note: when `keep (s.readReg64 .lr) = true` and `masterMemcpySpec.pre` holds, `ActiveRealRun`
     is false so `memcpyGhostHook` delegates to the `hookMemcpy` fallback rather than faulting;
     use `memcpyGhostHookK` (or `HooksDehook.MemcpyLrTrap` when `P_real` holds `blk20`) to rule out
     `keep (s.readReg64 .lr) = true`.
   - `memcpyGhostHookK keep P_real P_sub entryTarget`: wraps `memcpySpecK keep masterMemcpySpec`
     (`⌜keep (s.readReg64 .lr) = false⌝ ∗ masterMemcpySpec.pre`) with fallback `hookMemcpy`.
     `P_real` and `keep` are explicit parameters so both the F3 placed-CLI convention and the `K`
     route (`hole2_emptyProg` + `keepRange`) are 1-line instantiations.
2. **Pointwise state, VM & oracle preservation**:
   Proves `VmPreserved`, `OomPreserved ∧ PoolPreserved`, `.oracle = s.oracle`, `.fs = s.fs`,
   `.trace = s.trace`, and `HookFsTraced IsFsC` pointwise for both `memcpyGhostHook` and
   `memcpyGhostHookK`.
3. **Complete `HookOk` suite (plain, `withExecFrozen`, `*Budget`, `Acp`, and `memcpySpecK`)**:
   Covers all 6 base `memcpy` contracts (`libcMemcpySpec`, `sessionMemcpySpec`, `memcpyRegionSpec`,
   `sessionMemcpyRegionSpec`, `framelessMemcpySpec`, `SpqrV1.Alloc.sessionMemcpyRegionROSpec`),
   their 6 `*Budget` / `withVmPreserved` variants (plus flat `DefsBudget.framelessMemcpyBudgetSpec`),
   both `SpqrV1.Alloc.ConcatBudgetAux` `Acp` (`AllocCallPreserved ∧ VmPreserved`) contracts
   (`framelessMemcpyAcpSpec`, `sessionMemcpyRegionROSpec`), `Heap.allocMemcpyVmSpec`,
   `CliExt.memcpySpec` / `memcpyROSpec`, `Hkdf.memcpyROExtSpec`, `Hooks4K[Budget].sessionMemcpyROSpec4K`,
   `IfaceSimp.memcpyRegionCliSpec` / `libcMemcpyCliSpec`, and `.keepsFs` / `withStack` wrappers.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved stdMemcpySpec stdMemcpyROSpec)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (
  memcpySymWords stdMemcpy_ok_of_hasWords stdMemcpyRO_ok_of_hasWords
)
open CryptoVerification.LibsignalTripleRatchet (
  withStack
  sessionMemcpyRegionSpec sessionMemcpySpec framelessMemcpySpec memcpyROExtSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (memcpySpec memcpyROSpec)
open CryptoVerification.SignalSession.Cli.MainHops (hookOk_withStack)
open LibsignalBinary.Heap (
  FdsHiFrame VmPreserved OomPreserved PoolPreserved allocMemcpyVmSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookMemcpy_vmPreserved)
open LibsignalBinary.Heap.IfaceSimp (
  memcpyRegionCliSpec libcMemcpyCliSpec
  hookOk_withOomPoolPreserved hookMemcpy_preserves_oom_pool
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
  ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain keepMemsetBlk21
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec memcpySpecK
  pureWordsProg_memcpy_hasWords mallocngBlockProg20_hasWords
  mallocngBlockProg20_externAt_none pureWordsProg_externAt_none
  stdMemcpy_pre_of_masterMemcpy_pre stdMemcpyRO_pre_of_masterMemcpy_pre
  subroutine_ok_masterMemcpy_of_hasWords subroutine_ok_masterMemcpyK_of_hasWords
  hookMemcpy_masterMemcpy_ok hookMemcpy_masterMemcpyK_ok
  hookOk_memcpySpecK_of_plain
  hookOk_libcMemcpy_of_master
  hookOk_sessionMemcpy_of_master
  hookOk_cliMemcpy_of_master
  hookOk_memcpyRegion_of_master
  hookOk_sessionMemcpyRegion_of_master
  hookOk_framelessMemcpy_of_master
  hookOk_sessionMemcpyRegionRO_of_master
  hookOk_memcpyROExt_of_master
  hookOk_cliMemcpyRO_of_master
  hookOk_sessionMemcpyRO4K_of_master
  hookOk_framelessMemcpyBudgetFlat_of_master
  hookOk_sessionMemcpyRO4KBudget_of_master
  hookOk_framelessMemcpyAcp_of_master
  hookOk_sessionMemcpyRegionROAcp_of_master
  hookOk_allocMemcpyVm_of_master
)

/-! ## 1. Ghost `memcpy` Hook Definitions & `keep` Coverage -/

/-- Plain ghost `memcpy` hook wrapping `masterMemcpySpec` via `linkedCallHook` with fallback
    `hookMemcpy`. Parametric in `keep`, `P_real`, `P_sub`, and `entryTarget` (typically
    `mmpl.base 20`). Note: if `keep (s.readReg64 .lr) = true` while `masterMemcpySpec.pre` holds,
    `ActiveRealRun` fails and this hook delegates to `hookMemcpy`; use `memcpyGhostHookK` when the
    ghost run itself must reject `keep (s.readReg64 .lr) = true` via `.Exception`. -/
@[expose] noncomputable def memcpyGhostHook
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  linkedCallHook keep P_real P_sub entryTarget masterMemcpySpec hookMemcpy

/-- `K`-narrowed ghost `memcpy` hook wrapping `memcpySpecK keep masterMemcpySpec` via
    `linkedCallHook` with fallback `hookMemcpy`. Outside `keep (s.readReg64 .lr) = false` (or when
    `masterMemcpySpec.pre` fails), transitions to `.Exception` so any non-`.Exception` ghost run
    automatically witnesses `keep (u.readReg64 .lr) = false` at every call site. -/
@[expose] noncomputable def memcpyGhostHookK
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  linkedCallHook keep P_real P_sub entryTarget (memcpySpecK keep masterMemcpySpec) hookMemcpy

/-- Specialization of `memcpyGhostHook` to `P_sub = mallocngBlockProg mmpl 20 Syscall.standard` at
    `mmpl.base 20`. -/
noncomputable abbrev memcpyGhostHookBlk20
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memcpyGhostHook keep P_real (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)

/-- Specialization of `memcpyGhostHookK` to `P_sub = mallocngBlockProg mmpl 20 Syscall.standard` at
    `mmpl.base 20`. -/
noncomputable abbrev memcpyGhostHookBlk20K
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memcpyGhostHookK keep P_real (mallocngBlockProg mmpl 20 Syscall.standard) (mmpl.base 20)

/-- Specialization of `memcpyGhostHook` to `P_sub = pureWordsProg (mmpl.base 20) memcpySymWords`. -/
noncomputable abbrev memcpyGhostHookPure20
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memcpyGhostHook keep P_real (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20)

/-- Specialization of `memcpyGhostHookK` to `P_sub = pureWordsProg (mmpl.base 20) memcpySymWords`. -/
noncomputable abbrev memcpyGhostHookPure20K
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memcpyGhostHookK keep P_real (pureWordsProg (mmpl.base 20) memcpySymWords) (mmpl.base 20)

/-- Minimal placement-generic `keep` predicate retaining only the 396-byte `memcpy` block (`blk20`). -/
@[expose] def keepMemcpyBlk20 (mmpl : Obj.MultiPlacement) (a : BitVec 64) : Bool :=
  decide ((a - mmpl.base 20).toNat < 396)

/-- Combined placement-generic `keep` predicate retaining both `blk20` (`memcpy`, 396 B) and
    `blk21` (`memset`, 260 B). -/
@[expose] def keepMemOps (mmpl : Obj.MultiPlacement) (a : BitVec 64) : Bool :=
  keepMemcpyBlk20 mmpl a || keepMemsetBlk21 mmpl a

/-- Coverage condition stating that `keep` retains all 396 bytes of `mallocngLib` block 20. -/
@[expose] def KeepCoversBlk20 (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) : Prop :=
  ∀ off : Nat, off < 396 → keep (mmpl.base 20 + BitVec.ofNat 64 off) = true

theorem keepCoversBlk20_keepMemcpyBlk20 (mmpl : Obj.MultiPlacement) :
    KeepCoversBlk20 (keepMemcpyBlk20 mmpl) mmpl := by
  intro off hoff
  unfold keepMemcpyBlk20
  have hsub : mmpl.base 20 + BitVec.ofNat 64 off - mmpl.base 20 = BitVec.ofNat 64 off := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hoff

theorem keepCoversBlk20_keepMemOps (mmpl : Obj.MultiPlacement) :
    KeepCoversBlk20 (keepMemOps mmpl) mmpl := by
  intro off hoff
  unfold keepMemOps
  rw [keepCoversBlk20_keepMemcpyBlk20 mmpl off hoff, Bool.true_or]

theorem keepCoversBlk20_of_inRegion
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement}
    (hin : ∀ a : BitVec 64, InRegion (mmpl.base 20) 396 a → keep a = true) :
    KeepCoversBlk20 keep mmpl := by
  intro off hoff
  apply hin
  unfold InRegion
  have hsub : mmpl.base 20 + BitVec.ofNat 64 off - mmpl.base 20 = BitVec.ofNat 64 off := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hoff

theorem keepCoversBlk20_of_range
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} (lo hi : Nat)
    (hrange : ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → keep a = true)
    (hlo : lo ≤ (mmpl.base 20).toNat)
    (hhi : (mmpl.base 20).toNat + 396 ≤ hi)
    (hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64) :
    KeepCoversBlk20 keep mmpl := by
  intro off hoff
  have hadd : (mmpl.base 20 + BitVec.ofNat 64 off).toNat = (mmpl.base 20).toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (mmpl.base 20).toNat + off < 2 ^ 64)]
  exact hrange _ (by omega) (by omega)

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, & PC Invariance -/

theorem specStripSInvariant_masterMemcpy (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterMemcpySpec where
  pre_eq := fun ⟨_, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterMemcpyK (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (memcpySpecK keep masterMemcpySpec) where
  pre_eq := fun ⟨_, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterMemcpy :
    SpecPreservesFsTrace masterMemcpySpec := by
  intro ⟨ro, dst, src, bs⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterMemcpySpec] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.2.1
    have htr : sf.trace = s0.trace := hpost.1.2.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [masterMemcpySpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [masterMemcpySpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [masterMemcpySpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem specPreservesFsTrace_masterMemcpyK (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (memcpySpecK keep masterMemcpySpec) :=
  specPreservesFsTrace_masterMemcpy

theorem masterMemcpy_pre_setPC (x : Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) (s : State)
    (pc : BitVec 64) :
    masterMemcpySpec.pre x (s.setPC pc) = masterMemcpySpec.pre x s := by
  rcases x with ⟨_, _, _, _⟩; cases s; rfl

theorem masterMemcpyK_pre_setPC (keep : BitVec 64 → Bool)
    (x : Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) (s : State) (pc : BitVec 64) :
    (memcpySpecK keep masterMemcpySpec).pre x (s.setPC pc) =
      (memcpySpecK keep masterMemcpySpec).pre x s := by
  rcases x with ⟨_, _, _, _⟩; cases s; rfl

theorem masterMemcpy_outcome_setPC (x : Bool × BitVec 64 × BitVec 64 × List (BitVec 8))
    (R : SepProp) (s0 sf : State) (pc : BitVec 64) :
    SubroutineOutcome masterMemcpySpec x R (s0.setPC pc) sf →
      SubroutineOutcome masterMemcpySpec x R s0 sf := by
  rcases x with ⟨_, _, _, _⟩; cases s0; exact id

theorem masterMemcpyK_outcome_setPC (keep : BitVec 64 → Bool)
    (x : Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) (R : SepProp) (s0 sf : State)
    (pc : BitVec 64) :
    SubroutineOutcome (memcpySpecK keep masterMemcpySpec) x R (s0.setPC pc) sf →
      SubroutineOutcome (memcpySpecK keep masterMemcpySpec) x R s0 sf := by
  rcases x with ⟨_, _, _, _⟩; cases s0; exact id

theorem keepFsTrace_hookMemcpy_eq (s0 : State) :
    keepFsTrace hookMemcpy s0 = hookMemcpy s0 := by
  cases s0; rfl

theorem keepFsTrace_hookMemcpy_master_ok :
    HookOk (keepFsTrace hookMemcpy) masterMemcpySpec := by
  have hfn : keepFsTrace hookMemcpy = hookMemcpy := funext keepFsTrace_hookMemcpy_eq
  rw [hfn]
  exact hookMemcpy_masterMemcpy_ok

theorem keepFsTrace_hookMemcpy_masterK_ok (keep : BitVec 64 → Bool) :
    HookOk (keepFsTrace hookMemcpy) (memcpySpecK keep masterMemcpySpec) := by
  have hfn : keepFsTrace hookMemcpy = hookMemcpy := funext keepFsTrace_hookMemcpy_eq
  rw [hfn]
  exact hookMemcpy_masterMemcpyK_ok keep

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`VmPreserved`, `OomPreserved`, `oracle`) -/

theorem memcpyGhostHook_master_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) masterMemcpySpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemcpy_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemcpy keep)
    specPreservesFsTrace_masterMemcpy
    masterMemcpy_pre_setPC
    masterMemcpy_outcome_setPC
    keepFsTrace_hookMemcpy_master_ok

theorem memcpyGhostHookK_masterK_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords) :
    HookOk (memcpyGhostHookK keep P_real P_sub entryTarget)
      (memcpySpecK keep masterMemcpySpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemcpyK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemcpyK keep)
    (specPreservesFsTrace_masterMemcpyK keep)
    (masterMemcpyK_pre_setPC keep)
    (masterMemcpyK_outcome_setPC keep)
    (keepFsTrace_hookMemcpy_masterK_ok keep)

theorem memcpyGhostHook_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (memcpyGhostHook keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget masterMemcpySpec hookMemcpy s0

theorem memcpyGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (memcpyGhostHookK keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget (memcpySpecK keep masterMemcpySpec) hookMemcpy s0

theorem memcpyGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (memcpyGhostHook keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget masterMemcpySpec hookMemcpy

theorem memcpyGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (memcpyGhostHookK keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget (memcpySpecK keep masterMemcpySpec) hookMemcpy

private theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst
        rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
        rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_pureAbortOutcome {α : Type} {spec : Spec α}
    (hpan0 : spec.onPanic = fun _ _ _ => ⌜False⌝)
    (hex0 : spec.onExit = fun _ _ _ _ => ⌜False⌝)
    (hoom0 : spec.onOom = fun _ _ _ => ⌜False⌝)
    {x : α} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome spec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · rw [hpan0] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · rw [hex0] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · rw [hoom0] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Shared real-run `StdStatePreserved` + `oracle` equality extractor when `s0` satisfies
    `masterMemcpySpec.pre` and `ActiveRealRun keep P_real P_sub entryTarget s0`. -/
private theorem activeRealRun_stdStatePreserved_and_oracle
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    {x : Bool × BitVec 64 × BitVec 64 × List (BitVec 8)} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterMemcpySpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keep P_real P_sub entryTarget s0) :
    StdStatePreserved s0 (Classical.choose hReal.2.2.2) ∧
    (Classical.choose hReal.2.2.2).oracle = s0.oracle := by
  rcases x with ⟨ro, dst, src, bs⟩
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  cases ro
  · have hpre : s0.mem ⊨ stdMemcpySpec.pre (dst, src, bs) s0 ∗ R :=
      stdMemcpy_pre_of_masterMemcpy_pre hpreM
    have hs1_pre : s1.mem ⊨ stdMemcpySpec.pre (dst, src, bs) s1 ∗ R := by
      cases s0; exact hpre
    have hs1'_pre : s1'.mem ⊨ stdMemcpySpec.pre (dst, src, bs) s1' ∗ R := by
      have hsat := satisfies_stripExecOutside keep hs1_pre
      have heq : stdMemcpySpec.pre (dst, src, bs) s1' = stdMemcpySpec.pre (dst, src, bs) s1 := by
        dsimp only [s1']; cases s1; rfl
      rwa [heq]
    obtain ⟨sf', hsteps', hout'⟩ :=
      subroutine_ok_elim_steps_outcome
        (stdMemcpy_ok_of_hasWords P_sub entryTarget hsub_no hwords)
        (dst, src, bs) R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
    obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_pureAbortOutcome rfl rfl rfl hout'
    have hstop0' : SubroutineStop s0 sf' := hstop1'
    obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
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
    · dsimp only [stdMemcpySpec] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
      have hstd' : StdStatePreserved s1' sf' := hpost'.1.2
      rw [hsf_eq] at hstd'
      have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
        perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
          hstd'.2.2.2.2.2.2.2
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩, horc⟩
      · cases s0; cases sf; exact hstd'.1
      · cases s0; cases sf; exact hstd'.2.1
      · cases s0; cases sf; exact hstd'.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.2.2.2.1
    · dsimp only [stdMemcpySpec] at hpan
      rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
    · dsimp only [stdMemcpySpec] at hex
      rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
    · dsimp only [stdMemcpySpec] at hoom
      rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1
  · have hpre : s0.mem ⊨ stdMemcpyROSpec.pre (dst, src, bs) s0 ∗ R :=
      stdMemcpyRO_pre_of_masterMemcpy_pre hpreM
    have hs1_pre : s1.mem ⊨ stdMemcpyROSpec.pre (dst, src, bs) s1 ∗ R := by
      cases s0; exact hpre
    have hs1'_pre : s1'.mem ⊨ stdMemcpyROSpec.pre (dst, src, bs) s1' ∗ R := by
      have hsat := satisfies_stripExecOutside keep hs1_pre
      have heq : stdMemcpyROSpec.pre (dst, src, bs) s1' = stdMemcpyROSpec.pre (dst, src, bs) s1 := by
        dsimp only [s1']; cases s1; rfl
      rwa [heq]
    obtain ⟨sf', hsteps', hout'⟩ :=
      subroutine_ok_elim_steps_outcome
        (stdMemcpyRO_ok_of_hasWords P_sub entryTarget hsub_no hwords)
        (dst, src, bs) R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
    obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_pureAbortOutcome rfl rfl rfl hout'
    have hstop0' : SubroutineStop s0 sf' := hstop1'
    obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
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
    · dsimp only [stdMemcpyROSpec] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
      have hstd' : StdStatePreserved s1' sf' := hpost'.1.2
      rw [hsf_eq] at hstd'
      have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
        perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
          hstd'.2.2.2.2.2.2.2
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩, horc⟩
      · cases s0; cases sf; exact hstd'.1
      · cases s0; cases sf; exact hstd'.2.1
      · cases s0; cases sf; exact hstd'.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.2.2.1
      · cases s0; cases sf; exact hstd'.2.2.2.2.2.2.1
    · dsimp only [stdMemcpyROSpec] at hpan
      rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
    · dsimp only [stdMemcpyROSpec] at hex
      rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
    · dsimp only [stdMemcpyROSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

/-- Pointwise `VmPreserved` for `memcpyGhostHook` across all three branches. -/
theorem memcpyGhostHook_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    VmPreserved s0 (memcpyGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold memcpyGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre hReal).1
    · rw [keepFsTrace_hookMemcpy_eq]
      exact hookMemcpy_vmPreserved s0
  · exact VmPreserved.refl s0

/-- Pointwise `VmPreserved` for `memcpyGhostHookK` across all three branches. -/
theorem memcpyGhostHookK_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    VmPreserved s0 (memcpyGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold memcpyGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memcpySpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_hookMemcpy_eq]
      exact hookMemcpy_vmPreserved s0
  · exact VmPreserved.refl s0

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memcpyGhostHook`. -/
theorem memcpyGhostHook_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    OomPreserved s0 (memcpyGhostHook keep P_real P_sub entryTarget s0) ∧
    PoolPreserved s0 (memcpyGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold memcpyGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre hReal).1
    · rw [keepFsTrace_hookMemcpy_eq]
      exact hookMemcpy_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memcpyGhostHookK`. -/
theorem memcpyGhostHookK_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    OomPreserved s0 (memcpyGhostHookK keep P_real P_sub entryTarget s0) ∧
    PoolPreserved s0 (memcpyGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold memcpyGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memcpySpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_hookMemcpy_eq]
      exact hookMemcpy_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `.oracle = s0.oracle` for `memcpyGhostHook`. -/
theorem memcpyGhostHook_oracle
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    (memcpyGhostHook keep P_real P_sub entryTarget s0).oracle = s0.oracle := by
  classical
  unfold memcpyGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre hReal).2
    · rw [keepFsTrace_hookMemcpy_eq]
      cases s0; rfl
  · rfl

/-- Pointwise `.oracle = s0.oracle` for `memcpyGhostHookK`. -/
theorem memcpyGhostHookK_oracle
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    (memcpyGhostHookK keep P_real P_sub entryTarget s0).oracle = s0.oracle := by
  classical
  unfold memcpyGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memcpySpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre.2 hReal).2
    · rw [keepFsTrace_hookMemcpy_eq]
      cases s0; rfl
  · rfl

/-- Pointwise `.trace = s0.trace` for `memcpyGhostHook`. -/
theorem memcpyGhostHook_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    (memcpyGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace :=
  (memcpyGhostHook_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords s0).1.2.1

/-- Pointwise `.trace = s0.trace` for `memcpyGhostHookK`. -/
theorem memcpyGhostHookK_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (s0 : State) :
    (memcpyGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace :=
  (memcpyGhostHookK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords s0).1.2.1

/-- Along any non-`.Exception` call step of `memcpyGhostHookK`, `keep (u.readReg64 .lr) = false`
    holds automatically (the `K`-route `lr ∉ keep` extractor). -/
theorem memcpyGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg,
      (memcpyGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  classical
  have hActPre : ActiveRealPre (memcpySpecK keep masterMemcpySpec) u := by
    by_contra hnAct
    have hex : (memcpyGhostHookK keep P_real P_sub entryTarget u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold memcpyGhostHookK linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  rcases hActPre with ⟨_, _, _, _, hpre⟩
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of **plain** `memcpyGhostHook` when `keep (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterMemcpySpec s0` holds: `ActiveRealRun` is false, so `linkedCallHook`
    delegates to `keepFsTrace hookMemcpy s0 = hookMemcpy s0` (the fallback, NOT `.Exception`). -/
theorem memcpyGhostHook_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterMemcpySpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    memcpyGhostHook keep P_real P_sub entryTarget s0 = hookMemcpy s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keep P_real P_sub entryTarget s0 := by
    intro hReal
    have hfalse : keep (s0.readReg64 .lr) = false := hReal.2.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memcpyGhostHook linkedCallHook
  simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_hookMemcpy_eq s0

/-- Behavior of **`K`-narrowed** `memcpyGhostHookK` when `keep (s0.readReg64 .lr) = true`:
    always returns `{ s0 with status := .Exception "ghost-hook precondition violated" }`. -/
theorem memcpyGhostHookK_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    memcpyGhostHookK keep P_real P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (memcpySpecK keep masterMemcpySpec) s0 := by
    rintro ⟨_, _, _, _, hpre⟩
    dsimp only [memcpySpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keep (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memcpyGhostHookK linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-! ## 4. Complete `HookOk` Suite for All `memcpy` Consumer Contracts -/

section GenericHookOkSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memcpySymWords)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

-- 4.1 Base & CLI / Hkdf / Spqr plain contracts on `memcpyGhostHook`:

theorem memcpyGhostHook_libcMemcpy_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (libcMemcpySpec stk) :=
  hookOk_libcMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_sessionMemcpy_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (sessionMemcpySpec stk) :=
  hookOk_sessionMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_cliMemcpy_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpySpec :=
  hookOk_cliMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyRegion_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyRegionSpec :=
  hookOk_memcpyRegion_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRegion_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) sessionMemcpyRegionSpec :=
  hookOk_sessionMemcpyRegion_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_framelessMemcpy_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) framelessMemcpySpec :=
  hookOk_framelessMemcpy_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRegionRO_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  hookOk_sessionMemcpyRegionRO_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyROExt_ok (stk : Nat := 16384) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (memcpyROExtSpec stk) :=
  hookOk_memcpyROExt_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_cliMemcpyRO_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyROSpec :=
  hookOk_cliMemcpyRO_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRO4K_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyROSpec4K :=
  hookOk_sessionMemcpyRO4K_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

-- 4.2 `.keepsFs` & `withStack` plain variants on `memcpyGhostHook`:

theorem memcpyGhostHook_libcMemcpy_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (libcMemcpySpec stk).keepsFs :=
  (memcpyGhostHook_libcMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpy_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (sessionMemcpySpec stk).keepsFs :=
  (memcpyGhostHook_sessionMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_cliMemcpy_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpySpec.keepsFs :=
  (memcpyGhostHook_cliMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_memcpyRegion_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyRegionSpec.keepsFs :=
  (memcpyGhostHook_memcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_memcpyRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (withStack memcpyRegionSpec stk) :=
  hookOk_withStack
    (memcpyGhostHook_memcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_memcpyRegion_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack memcpyRegionSpec stk).keepsFs :=
  (memcpyGhostHook_memcpyRegion_withStack_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpyRegion_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) sessionMemcpyRegionSpec.keepsFs :=
  (memcpyGhostHook_sessionMemcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpyRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemcpyRegionSpec stk) :=
  hookOk_withStack
    (memcpyGhostHook_sessionMemcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_sessionMemcpyRegion_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemcpyRegionSpec stk).keepsFs :=
  (memcpyGhostHook_sessionMemcpyRegion_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_framelessMemcpy_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) framelessMemcpySpec.keepsFs :=
  (memcpyGhostHook_framelessMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpyRegionRO_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec.keepsFs :=
  (memcpyGhostHook_sessionMemcpyRegionRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpyRegionRO_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk) :=
  hookOk_withStack
    (memcpyGhostHook_sessionMemcpyRegionRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_sessionMemcpyRegionRO_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs :=
  (memcpyGhostHook_sessionMemcpyRegionRO_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_memcpyROExt_keepsFs_ok (stk : Nat := 16384) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (memcpyROExtSpec stk).keepsFs :=
  (memcpyGhostHook_memcpyROExt_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_cliMemcpyRO_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyROSpec.keepsFs :=
  (memcpyGhostHook_cliMemcpyRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

-- 4.3 `*Budget` (`withVmPreserved`), `Acp` (`AllocCallPreserved ∧ VmPreserved`), & `OomPool`:

theorem memcpyGhostHook_libcMemcpy_budget_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (libcMemcpySpec stk)) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_libcMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_libcMemcpy_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (libcMemcpySpec stk)).keepsFs :=
  (memcpyGhostHook_libcMemcpy_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpyBudget_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (sessionMemcpyBudgetSpec stk) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_sessionMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyBudget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (sessionMemcpyBudgetSpec stk).keepsFs :=
  (memcpyGhostHook_sessionMemcpyBudget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_cliMemcpy_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (withVmPreserved memcpySpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_cliMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyRegion_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved memcpyRegionSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_memcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyRegion_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved memcpyRegionSpec) stk) :=
  hookOk_withStack
    (memcpyGhostHook_memcpyRegion_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_memcpyRegion_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved memcpyRegionSpec) stk).keepsFs :=
  (memcpyGhostHook_memcpyRegion_budget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_sessionMemcpyRegionBudget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) sessionMemcpyRegionBudgetSpec :=
  hookOk_withVmPreserved
    (memcpyGhostHook_sessionMemcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRegionBudget_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemcpyRegionBudgetSpec stk) :=
  hookOk_withStack
    (memcpyGhostHook_sessionMemcpyRegionBudget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memcpyGhostHook_sessionMemcpyRegionBudget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemcpyRegionBudgetSpec stk).keepsFs :=
  (memcpyGhostHook_sessionMemcpyRegionBudget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_framelessMemcpyBudget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) framelessMemcpyBudgetSpec :=
  hookOk_withVmPreserved
    (memcpyGhostHook_framelessMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_framelessMemcpyBudget_keepsFs_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) framelessMemcpyBudgetSpec.keepsFs :=
  (memcpyGhostHook_framelessMemcpyBudget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_framelessMemcpyBudgetFlat_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec :=
  hookOk_framelessMemcpyBudgetFlat_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRegionRO_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_sessionMemcpyRegionRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk) :=
  hookOk_withStack
    (memcpyGhostHook_sessionMemcpyRegionRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    stk

theorem memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withStack
        (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) stk).keepsFs :=
  (memcpyGhostHook_sessionMemcpyRegionRO_budget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memcpyGhostHook_fs keep P_real P_sub entryTarget)

theorem memcpyGhostHook_memcpyROExt_budget_ok (stk : Nat := 16384) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (memcpyROExtSpec stk)) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_memcpyROExt_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_cliMemcpyRO_budget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (withVmPreserved memcpyROSpec) :=
  hookOk_withVmPreserved
    (memcpyGhostHook_cliMemcpyRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRO4KBudget_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget.sessionMemcpyROSpec4K :=
  hookOk_sessionMemcpyRO4KBudget_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_framelessMemcpyAcp_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec :=
  hookOk_framelessMemcpyAcp_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_sessionMemcpyRegionROAcp_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget)
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec :=
  hookOk_sessionMemcpyRegionROAcp_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_allocMemcpyVm_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) allocMemcpyVmSpec :=
  hookOk_allocMemcpyVm_of_master
    (memcpyGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_oracle hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_memcpyRegionCli_ok :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) memcpyRegionCliSpec :=
  hookOk_withOomPoolPreserved
    (memcpyGhostHook_memcpyRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memcpyGhostHook_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memcpyGhostHook_libcMemcpyCli_ok (stk : Nat := 4096) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (libcMemcpyCliSpec stk) :=
  hookOk_withOomPoolPreserved
    (memcpyGhostHook_libcMemcpy_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memcpyGhostHook_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

-- 4.4 `withExecFrozen` corollaries on `memcpyGhostHook`:

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memcpyGhostHook_any_execFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memcpyGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memcpyGhostHook_any_memcpySpecK_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memcpyGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (memcpyGhostHook keep P_real P_sub entryTarget) (memcpySpecK keep spec) :=
  hookOk_memcpySpecK_of_plain keep hh

end GenericHookOkSuite

/-! ## 5. `mallocngBlockProg mmpl 20` & `pureWordsProg` Specializations -/

theorem memcpyGhostHookBlk20_master_ok
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (memcpyGhostHookBlk20 keep P_real mmpl) masterMemcpySpec :=
  memcpyGhostHook_master_ok hsvc_real rfl hreal_no
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem memcpyGhostHookBlk20K_masterK_ok
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (memcpyGhostHookBlk20K keep P_real mmpl) (memcpySpecK keep masterMemcpySpec) :=
  memcpyGhostHookK_masterK_ok hsvc_real rfl hreal_no
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem memcpyGhostHookPure20_master_ok
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (memcpyGhostHookPure20 keep P_real mmpl) masterMemcpySpec :=
  memcpyGhostHook_master_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

theorem memcpyGhostHookPure20K_masterK_ok
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : Obj.MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (memcpyGhostHookPure20K keep P_real mmpl) (memcpySpecK keep masterMemcpySpec) :=
  memcpyGhostHookK_masterK_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
