/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine

/-!
# Ghost `memset` Hook, `HookOk` Suite & `GhostExternReplays` (`HooksDehook.MemsetGhost`)

Design-independent Steps 2–4 for de-hooking `memset` (`VerifiedLibraries.mallocngLib` block 21)
using `linkedCallHook` (`AllocGhostLinkTransfer.lean`):

1. **Ghost `memset` hooks (`memsetGhostHook`, `memsetGhostHookK`)**:
   - `memsetGhostHook keep P_real P_sub entryTarget`: wraps `masterMemsetSpec` with fallback
     `hookMemset`.
   - `memsetGhostHookK keep P_real P_sub entryTarget`: wraps the `K`-narrowed specification
     `memsetSpecK keep masterMemsetSpec` (`⌜keep (s.readReg64 .lr) = false⌝ ∗ masterMemsetSpec.pre`)
     with fallback `hookMemset`, ready to slot in as an 8th `K`-ghost on the `K` route
     (e.g. `keep := hole2_keepSub`).
2. **Pointwise state & VM preservation**:
   Proves `VmPreserved`, `OomPreserved ∧ PoolPreserved`, `.fs = s.fs`, `.trace = s.trace`, and
   `HookFsTraced IsFsC` pointwise for both `memsetGhostHook` and `memsetGhostHookK` by combining
   `stdMemsetSpec`'s `StdStatePreserved` with `KeepsFrozen` + `ExecFrozen` across `stripS keep`.
3. **Complete `HookOk` suite (plain, `withExecFrozen`, and `memsetSpecK`-narrowed)**:
   Covers `libcMemsetSpec`, `sessionMemsetSpec`, `CliExt.memsetSpec`, `memsetRegionSpec`,
   `sessionMemsetRegionSpec`, `withVmPreserved` / `*BudgetSpec` variants, `.keepsFs` wrappers,
   `withStack` wrappers, and `memsetRegionCliSpec` / `libcMemsetCliSpec`.
4. **`GhostExternReplays` arm**:
   Instantiates `ghostExternReplays_of_linkedCallHook` for `memsetGhostHook` and `memsetGhostHookK`
   with `keep (u.readReg64 .lr) = false` as an explicit hypothesis, discharging all `P_sub` and
   spec-side obligations (`hsvc_sub`, `hsub_no`, `hOk`, `hSpecInv`, `hFsT`, `hPrePC`, `hOutPC`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved stdMemsetSpec)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification.LibsignalTripleRatchet (
  withStack
  sessionMemsetRegionSpec sessionMemsetSpec
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (session2MemsetExternSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemsetRegionBudgetSpec sessionMemsetBudgetSpec
)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (memsetSpec)
open CryptoVerification.SignalSession.Cli.MainHops (hookOk_withStack)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookMemset_vmPreserved)
open LibsignalBinary.Heap.IfaceSimp (
  memsetRegionCliSpec libcMemsetCliSpec
  hookOk_withOomPoolPreserved hookMemset_preserves_oom_pool
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
  ActiveRealPre ActiveRealRun StubReachesTarget
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved masterMemsetSpec memsetSpecK
  pureWordsProg_memset_hasWords mallocngBlockProg21_hasWords
  mallocngBlockProg21_externAt_none pureWordsProg_externAt_none
  stdMemset_pre_of_masterMemset_pre
  subroutine_ok_stdMemset_of_hasWords subroutine_ok_masterMemset_of_hasWords
  subroutine_ok_masterMemsetK_of_hasWords
  hookMemset_masterMemset_ok hookMemset_masterMemsetK_ok
  hookOk_memsetSpecK_of_plain
  hookOk_libcMemset_of_master hookOk_libcMemsetK_of_master
  hookOk_sessionMemset_of_master hookOk_sessionMemsetK_of_master
  hookOk_cliMemset_of_master hookOk_cliMemsetK_of_master
  hookOk_memsetRegion_of_master hookOk_memsetRegionK_of_master
  hookOk_sessionMemsetRegion_of_master hookOk_sessionMemsetRegionK_of_master
  hookOk_session2MemsetExtern_of_master hookOk_session2MemsetExternK_of_master
  memsetSpecK_keepsFs memsetSpecK_withVmPreserved
  memsetSpecK_sessionMemsetBudget memsetSpecK_sessionMemsetRegionBudget
)

/-- `ExecFrozen` precondition wrapper: conjoins `⌜ExecFrozen s.mem⌝` to `spec.pre`. -/
@[expose] def withExecFrozen {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜ExecFrozen s.mem⌝ ∗ spec.pre x s }

/-- Any `HookOk f spec` weakens to `HookOk f (withExecFrozen spec)`. -/
theorem hookOk_withExecFrozen_of_plain {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f spec) :
    HookOk f (withExecFrozen spec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [withExecFrozen] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hh x R s0 hrun hpre.2 hsp

/-! ## 1. Ghost `memset` Hook Definitions & `keep` Coverage -/

/-- Plain ghost `memset` hook wrapping `masterMemsetSpec` via `linkedCallHook` with fallback
    `hookMemset`. Parametric in `keep`, `P_real`, `P_sub`, and `entryTarget` (typically
    `mmpl.base 21`). -/
@[expose] noncomputable def memsetGhostHook
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  linkedCallHook keep P_real P_sub entryTarget masterMemsetSpec hookMemset

/-- `K`-narrowed ghost `memset` hook wrapping `memsetSpecK keep masterMemsetSpec` via
    `linkedCallHook` with fallback `hookMemset`. Outside `keep (s.readReg64 .lr) = false` (or when
    `masterMemsetSpec.pre` fails), transitions to `.Exception` so any non-`.Exception` ghost run
    automatically witnesses `keep (u.readReg64 .lr) = false` at every call site. -/
@[expose] noncomputable def memsetGhostHookK
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  linkedCallHook keep P_real P_sub entryTarget (memsetSpecK keep masterMemsetSpec) hookMemset

/-- Specialization of `memsetGhostHook` to `P_sub = mallocngBlockProg mmpl 21 Syscall.standard` at
    `mmpl.base 21`. -/
noncomputable abbrev memsetGhostHookBlk21
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memsetGhostHook keep P_real (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)

/-- Specialization of `memsetGhostHookK` to `P_sub = mallocngBlockProg mmpl 21 Syscall.standard` at
    `mmpl.base 21`. -/
noncomputable abbrev memsetGhostHookBlk21K
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memsetGhostHookK keep P_real (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21)

/-- Specialization of `memsetGhostHook` to `P_sub = pureWordsProg (mmpl.base 21) memsetWordsSym`. -/
noncomputable abbrev memsetGhostHookPure21
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memsetGhostHook keep P_real (pureWordsProg (mmpl.base 21) memsetWordsSym) (mmpl.base 21)

/-- Specialization of `memsetGhostHookK` to `P_sub = pureWordsProg (mmpl.base 21) memsetWordsSym`. -/
noncomputable abbrev memsetGhostHookPure21K
    (keep : BitVec 64 → Bool) (P_real : Program) (mmpl : Obj.MultiPlacement) : State → State :=
  memsetGhostHookK keep P_real (pureWordsProg (mmpl.base 21) memsetWordsSym) (mmpl.base 21)

/-- Minimal placement-generic `keep` predicate retaining only the 260-byte `memset` block (`blk21`). -/
@[expose] def keepMemsetBlk21 (mmpl : Obj.MultiPlacement) (a : BitVec 64) : Bool :=
  decide ((a - mmpl.base 21).toNat < 260)

/-- Full `mallocngLib` placement-generic `keep` predicate. -/
@[expose] def keepMallocng (mmpl : Obj.MultiPlacement) (a : BitVec 64) : Bool :=
  (mallocngLib.findCodeBlock mmpl a).isSome

/-- Coverage condition stating that `keep` retains all 260 bytes of `mallocngLib` block 21
    (satisfied by `hole2_keepSub`, `keepMallocng mmpl`, and `keepMemsetBlk21 mmpl`). -/
@[expose] def KeepCoversBlk21 (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) : Prop :=
  ∀ off : Nat, off < 260 → keep (mmpl.base 21 + BitVec.ofNat 64 off) = true

theorem keepCoversBlk21_keepMemsetBlk21 (mmpl : Obj.MultiPlacement) :
    KeepCoversBlk21 (keepMemsetBlk21 mmpl) mmpl := by
  intro off hoff
  unfold keepMemsetBlk21
  have hsub : mmpl.base 21 + BitVec.ofNat 64 off - mmpl.base 21 = BitVec.ofNat 64 off := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hoff

/-- Sufficient condition for `KeepCoversBlk21 keep mmpl` from `InRegion (mmpl.base 21) 260`
    (matching the `∀ a, InRegion (mmpl.base 21) 260 a → keep a = true` signature). -/
theorem keepCoversBlk21_of_inRegion
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement}
    (hin : ∀ a : BitVec 64, InRegion (mmpl.base 21) 260 a → keep a = true) :
    KeepCoversBlk21 keep mmpl := by
  intro off hoff
  apply hin
  unfold InRegion
  have hsub : mmpl.base 21 + BitVec.ofNat 64 off - mmpl.base 21 = BitVec.ofNat 64 off := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hoff

/-- Sufficient condition for `KeepCoversBlk21 keep mmpl` from any half-open address range
    `[lo, hi)` on which `keep` evaluates to `true` (e.g. `hole2_keepSub` on the `K`-route). -/
theorem keepCoversBlk21_of_range
    {keep : BitVec 64 → Bool} {mmpl : Obj.MultiPlacement} (lo hi : Nat)
    (hrange : ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → keep a = true)
    (hlo : lo ≤ (mmpl.base 21).toNat)
    (hhi : (mmpl.base 21).toNat + 260 ≤ hi)
    (hnowrap : (mmpl.base 21).toNat + 260 ≤ 2 ^ 64) :
    KeepCoversBlk21 keep mmpl := by
  intro off hoff
  have hadd : (mmpl.base 21 + BitVec.ofNat 64 off).toNat = (mmpl.base 21).toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (mmpl.base 21).toNat + off < 2 ^ 64)]
  exact hrange _ (by omega) (by omega)

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, & PC Invariance -/

theorem specStripSInvariant_masterMemset (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterMemsetSpec where
  pre_eq := fun ⟨_, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterMemsetK (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (memsetSpecK keep masterMemsetSpec) where
  pre_eq := fun ⟨_, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterMemset :
    SpecPreservesFsTrace masterMemsetSpec := by
  intro ⟨dst, byteVal, len⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterMemsetSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.2.1
    have htr : sf.trace = s0.trace := hpost.1.2.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [masterMemsetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [masterMemsetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [masterMemsetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem specPreservesFsTrace_masterMemsetK (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (memsetSpecK keep masterMemsetSpec) :=
  specPreservesFsTrace_masterMemset

theorem masterMemset_pre_setPC (x : BitVec 64 × BitVec 8 × Nat) (s : State)
    (pc : BitVec 64) :
    masterMemsetSpec.pre x (s.setPC pc) = masterMemsetSpec.pre x s := by
  rcases x with ⟨_, _, _⟩; cases s; rfl

theorem masterMemsetK_pre_setPC (keep : BitVec 64 → Bool)
    (x : BitVec 64 × BitVec 8 × Nat) (s : State) (pc : BitVec 64) :
    (memsetSpecK keep masterMemsetSpec).pre x (s.setPC pc) =
      (memsetSpecK keep masterMemsetSpec).pre x s := by
  rcases x with ⟨_, _, _⟩; cases s; rfl

theorem masterMemset_outcome_setPC (x : BitVec 64 × BitVec 8 × Nat) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterMemsetSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterMemsetSpec x R s0 sf := by
  rcases x with ⟨_, _, _⟩; cases s0; cases sf; exact h

theorem masterMemsetK_outcome_setPC (keep : BitVec 64 → Bool)
    (x : BitVec 64 × BitVec 8 × Nat) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (memsetSpecK keep masterMemsetSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (memsetSpecK keep masterMemsetSpec) x R s0 sf := by
  rcases x with ⟨_, _, _⟩; cases s0; cases sf; exact h

/-- `keepFsTrace hookMemset` is definitionally pointwise equal to `hookMemset` since `hookMemset`
    never modifies `fs` or `trace`. -/
theorem keepFsTrace_hookMemset_eq (s0 : State) :
    keepFsTrace hookMemset s0 = hookMemset s0 := by
  cases s0; rfl

theorem keepFsTrace_hookMemset_master_ok :
    HookOk (keepFsTrace hookMemset) masterMemsetSpec := by
  have hfn : keepFsTrace hookMemset = hookMemset := funext keepFsTrace_hookMemset_eq
  rw [hfn]
  exact hookMemset_masterMemset_ok

theorem keepFsTrace_hookMemset_masterK_ok (keep : BitVec 64 → Bool) :
    HookOk (keepFsTrace hookMemset) (memsetSpecK keep masterMemsetSpec) := by
  have hfn : keepFsTrace hookMemset = hookMemset := funext keepFsTrace_hookMemset_eq
  rw [hfn]
  exact hookMemset_masterMemsetK_ok keep

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`VmPreserved`, `OomPreserved`, `fs`) -/

/-- `HookOk` of `memsetGhostHook` for `masterMemsetSpec` on any hook-free `P_sub` holding
    `memsetWordsSym` at `entryTarget`. -/
theorem memsetGhostHook_master_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) masterMemsetSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemset keep)
    specPreservesFsTrace_masterMemset
    masterMemset_pre_setPC
    masterMemset_outcome_setPC
    keepFsTrace_hookMemset_master_ok

/-- `HookOk` of `memsetGhostHookK` for `memsetSpecK keep masterMemsetSpec` on any hook-free `P_sub`
    holding `memsetWordsSym` at `entryTarget`. -/
theorem memsetGhostHookK_masterK_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep masterMemsetSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemsetK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemsetK keep)
    (specPreservesFsTrace_masterMemsetK keep)
    (masterMemsetK_pre_setPC keep)
    (masterMemsetK_outcome_setPC keep)
    (keepFsTrace_hookMemset_masterK_ok keep)

theorem memsetGhostHook_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (memsetGhostHook keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget masterMemsetSpec hookMemset s0

theorem memsetGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (memsetGhostHookK keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget (memsetSpecK keep masterMemsetSpec) hookMemset s0

theorem memsetGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (memsetGhostHook keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget masterMemsetSpec hookMemset

theorem memsetGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (memsetGhostHookK keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget (memsetSpecK keep masterMemsetSpec) hookMemset

/-- Recover exact `Memory.perm` equality across `stripExecOutside keep` from `ExecFrozen` +
    `KeepsFrozen` + stripped-permission equality. -/
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

/-- Shared real-run `StdStatePreserved` + `mem.perm` equality extractor when `s0` satisfies
    `masterMemsetSpec.pre` and `ActiveRealRun keep P_real P_sub entryTarget s0`. -/
private theorem activeRealRun_stdStatePreserved
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
    StdStatePreserved s0 (Classical.choose hReal.2.2.2) := by
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
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [stdMemsetSpec] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : StdStatePreserved s1' sf' := hpost'.1.2
    rw [hsf_eq] at hstd'
    have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen hstd'.2.2.2.2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩
    · cases s0; cases sf; exact hstd'.1
    · cases s0; cases sf; exact hstd'.2.1
    · cases s0; cases sf; exact hstd'.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.2.2.1
  · dsimp only [stdMemsetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [stdMemsetSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [stdMemsetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

/-- Pointwise `VmPreserved` for `memsetGhostHook` across all three branches (`ActiveRealRun`,
    fallback `hookMemset`, and `.Exception`). -/
theorem memsetGhostHook_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    VmPreserved s0 (memsetGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold memsetGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre hReal)
    · rw [keepFsTrace_hookMemset_eq]
      exact hookMemset_vmPreserved s0
  · exact VmPreserved.refl s0

/-- Pointwise `VmPreserved` for `memsetGhostHookK` across all three branches. -/
theorem memsetGhostHookK_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    VmPreserved s0 (memsetGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold memsetGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_hookMemset_eq]
      exact hookMemset_vmPreserved s0
  · exact VmPreserved.refl s0

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memsetGhostHook`. -/
theorem memsetGhostHook_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    OomPreserved s0 (memsetGhostHook keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (memsetGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold memsetGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre hReal)
    · rw [keepFsTrace_hookMemset_eq]
      exact hookMemset_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memsetGhostHookK`. -/
theorem memsetGhostHookK_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    OomPreserved s0 (memsetGhostHookK keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (memsetGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold memsetGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hwords
          hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_hookMemset_eq]
      exact hookMemset_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `trace` preservation for `memsetGhostHook`. -/
theorem memsetGhostHook_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (memsetGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold memsetGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre hReal).2.1
    · rfl
  · rfl

/-- Pointwise `trace` preservation for `memsetGhostHookK`. -/
theorem memsetGhostHookK_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (s0 : State) :
    (memsetGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold memsetGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_stdStatePreserved hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre.2 hReal).2.1
    · rfl
  · rfl

/-- Along any non-`.Exception` call step of `memsetGhostHookK`, `keep (u.readReg64 .lr) = false`
    holds automatically (the `K`-route `lr ∉ keep` extractor). -/
theorem memsetGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {u : State}
    (hnoex : ∀ msg,
      (memsetGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  classical
  have hActPre : ActiveRealPre (memsetSpecK keep masterMemsetSpec) u := by
    by_contra hnAct
    have hex : (memsetGhostHookK keep P_real P_sub entryTarget u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold memsetGhostHookK linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  rcases hActPre with ⟨_, _, x, R, hpre⟩
  dsimp only [memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of **plain** `memsetGhostHook` when `keep (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterMemsetSpec s0` holds: `ActiveRealRun` is false, so `linkedCallHook`
    delegates to `keepFsTrace hookMemset s0 = hookMemset s0` (the **fallback**, NOT `.Exception`),
    which is why plain `HookOk (memsetGhostHook …) spec` holds unconditionally. -/
theorem memsetGhostHook_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterMemsetSpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    memsetGhostHook keep P_real P_sub entryTarget s0 = hookMemset s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keep P_real P_sub entryTarget s0 := by
    intro hReal
    have hfalse : keep (s0.readReg64 .lr) = false := hReal.2.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memsetGhostHook linkedCallHook
  simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_hookMemset_eq s0

/-- Behavior of **`K`-narrowed** `memsetGhostHookK` when `keep (s0.readReg64 .lr) = true`:
    `ActiveRealPre (memsetSpecK keep masterMemsetSpec) s0` is false regardless of memory contents,
    so `linkedCallHook` returns `{ s0 with status := .Exception "ghost-hook precondition violated" }`
    (an **exception**, NOT the fallback), which is why `memsetGhostHookK` satisfies `HookOk` only
    for `memsetSpecK keep spec` (and automatically witnesses `keep lr = false` under `hnoex`). -/
theorem memsetGhostHookK_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    memsetGhostHookK keep P_real P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (memsetSpecK keep masterMemsetSpec) s0 := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [memsetSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keep (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memsetGhostHookK linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-! ## 4. Complete `HookOk` Suite for All CLI `memset` Contracts -/

section GenericHookOkSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget memsetWordsSym)

include hsvc_real hsvc_sub hreal_no hsub_no hwords

-- 4.1 Plain contracts on `memsetGhostHook`:

theorem memsetGhostHook_libcMemset_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (libcMemsetSpec stk) :=
  hookOk_libcMemset_of_master
    (memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHook_sessionMemset_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (sessionMemsetSpec stk) :=
  hookOk_sessionMemset_of_master
    (memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHook_cliMemset_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) memsetSpec :=
  hookOk_cliMemset_of_master
    (memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_memsetRegion_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) memsetRegionSpec :=
  hookOk_memsetRegion_of_master
    (memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_sessionMemsetRegion_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) sessionMemsetRegionSpec :=
  hookOk_sessionMemsetRegion_of_master
    (memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_session2MemsetExtern_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (session2MemsetExternSpec stk) :=
  hookOk_session2MemsetExtern_of_master
    (memsetGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

-- 4.2 `.keepsFs` & `withStack` plain variants on `memsetGhostHook`:

theorem memsetGhostHook_libcMemset_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (libcMemsetSpec stk).keepsFs :=
  (memsetGhostHook_libcMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_sessionMemset_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (sessionMemsetSpec stk).keepsFs :=
  (memsetGhostHook_sessionMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_cliMemset_keepsFs_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) memsetSpec.keepsFs :=
  (memsetGhostHook_cliMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_memsetRegion_keepsFs_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) memsetRegionSpec.keepsFs :=
  (memsetGhostHook_memsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_sessionMemsetRegion_keepsFs_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) sessionMemsetRegionSpec.keepsFs :=
  (memsetGhostHook_sessionMemsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_session2MemsetExtern_keepsFs_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (session2MemsetExternSpec stk).keepsFs :=
  (memsetGhostHook_session2MemsetExtern_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_memsetRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (withStack memsetRegionSpec stk) :=
  hookOk_withStack
    (memsetGhostHook_memsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHook_sessionMemsetRegion_withStack_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemsetRegionSpec stk) :=
  hookOk_withStack
    (memsetGhostHook_sessionMemsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

-- 4.3 Budget / `withVmPreserved` & `.keepsFs` variants on `memsetGhostHook`:

theorem memsetGhostHook_libcMemset_budget_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (libcMemsetSpec stk)) :=
  hookOk_withVmPreserved
    (memsetGhostHook_libcMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_libcMemset_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (libcMemsetSpec stk)).keepsFs :=
  (memsetGhostHook_libcMemset_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_sessionMemsetBudget_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (sessionMemsetBudgetSpec stk) :=
  hookOk_withVmPreserved
    (memsetGhostHook_sessionMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_sessionMemsetBudget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (sessionMemsetBudgetSpec stk).keepsFs :=
  (memsetGhostHook_sessionMemsetBudget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_cliMemset_budget_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (withVmPreserved memsetSpec) :=
  hookOk_withVmPreserved
    (memsetGhostHook_cliMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_session2MemsetExtern_budget_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (session2MemsetExternSpec stk)) :=
  hookOk_withVmPreserved
    (memsetGhostHook_session2MemsetExtern_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_session2MemsetExtern_budget_keepsFs_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (session2MemsetExternSpec stk)).keepsFs :=
  (memsetGhostHook_session2MemsetExtern_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_memsetRegion_budget_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved memsetRegionSpec) :=
  hookOk_withVmPreserved
    (memsetGhostHook_memsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_memsetRegion_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved memsetRegionSpec) stk) :=
  hookOk_withStack
    (memsetGhostHook_memsetRegion_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHook_memsetRegion_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs :=
  (memsetGhostHook_memsetRegion_budget_withStack_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (memsetGhostHook_fs keep P_real P_sub entryTarget)

theorem memsetGhostHook_sessionMemsetRegionBudget_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) sessionMemsetRegionBudgetSpec :=
  hookOk_withVmPreserved
    (memsetGhostHook_sessionMemsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_sessionMemsetRegionBudget_withStack_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemsetRegionBudgetSpec stk) :=
  hookOk_withStack
    (memsetGhostHook_sessionMemsetRegionBudget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHook_sessionMemsetRegionBudget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withStack sessionMemsetRegionBudgetSpec stk).keepsFs :=
  (memsetGhostHook_sessionMemsetRegionBudget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHook_fs keep P_real P_sub entryTarget)

-- 4.4 `OomPreserved` / `PoolPreserved` CLI variants on `memsetGhostHook`:

theorem memsetGhostHook_memsetRegionCli_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) memsetRegionCliSpec :=
  hookOk_withOomPoolPreserved
    (memsetGhostHook_memsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHook_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_libcMemsetCli_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (libcMemsetCliSpec stk) :=
  hookOk_withOomPoolPreserved
    (memsetGhostHook_libcMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHook_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

-- 4.5 `withExecFrozen` corollaries on `memsetGhostHook`:

theorem memsetGhostHook_libcMemset_execFrozen_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withExecFrozen (libcMemsetSpec stk)) :=
  hookOk_withExecFrozen_of_plain
    (memsetGhostHook_libcMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)

theorem memsetGhostHook_sessionMemset_execFrozen_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withExecFrozen (sessionMemsetSpec stk)) :=
  hookOk_withExecFrozen_of_plain
    (memsetGhostHook_sessionMemset_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)

theorem memsetGhostHook_memsetRegion_execFrozen_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withExecFrozen memsetRegionSpec) :=
  hookOk_withExecFrozen_of_plain
    (memsetGhostHook_memsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_sessionMemsetRegion_execFrozen_ok :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withExecFrozen sessionMemsetRegionSpec) :=
  hookOk_withExecFrozen_of_plain
    (memsetGhostHook_sessionMemsetRegion_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHook_session2MemsetExtern_execFrozen_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget)
      (withExecFrozen (session2MemsetExternSpec stk)) :=
  hookOk_withExecFrozen_of_plain
    (memsetGhostHook_session2MemsetExtern_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)

-- 4.6 `K`-narrowed (`memsetSpecK keep spec`) contracts on `memsetGhostHook` (from plain `HookOk`
-- via `hookOk_memsetSpecK_of_plain`) AND on `memsetGhostHookK`:

omit hsvc_real hsvc_sub hreal_no hsub_no hwords in
theorem memsetGhostHook_any_memsetSpecK_ok {α : Type} {spec : Spec α}
    (hh : HookOk (memsetGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (memsetGhostHook keep P_real P_sub entryTarget) (memsetSpecK keep spec) :=
  hookOk_memsetSpecK_of_plain keep hh

theorem memsetGhostHookK_libcMemsetK_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (libcMemsetSpec stk)) :=
  hookOk_libcMemsetK_of_master keep
    (memsetGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHookK_sessionMemsetK_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetSpec stk)) :=
  hookOk_sessionMemsetK_of_master keep
    (memsetGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHookK_cliMemsetK_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep memsetSpec) :=
  hookOk_cliMemsetK_of_master keep
    (memsetGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_memsetRegionK_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep memsetRegionSpec) :=
  hookOk_memsetRegionK_of_master keep
    (memsetGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_sessionMemsetRegionK_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep sessionMemsetRegionSpec) :=
  hookOk_sessionMemsetRegionK_of_master keep
    (memsetGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_libcMemsetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (libcMemsetSpec stk).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_libcMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_sessionMemsetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetSpec stk).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_sessionMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_cliMemsetK_keepsFs_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep memsetSpec.keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_cliMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_memsetRegionK_keepsFs_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep memsetRegionSpec.keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_memsetRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_sessionMemsetRegionK_keepsFs_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep sessionMemsetRegionSpec.keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_sessionMemsetRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_libcMemsetK_budget_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (libcMemsetSpec stk))) := by
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memsetGhostHookK_libcMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_libcMemsetK_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (libcMemsetSpec stk)).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_libcMemsetK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_sessionMemsetBudgetK_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetBudgetSpec stk)) := by
  rw [← memsetSpecK_sessionMemsetBudget keep stk]
  exact hookOk_withVmPreserved
    (memsetGhostHookK_sessionMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_sessionMemsetBudgetK_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (sessionMemsetBudgetSpec stk).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_sessionMemsetBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_cliMemsetK_budget_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved memsetSpec)) := by
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memsetGhostHookK_cliMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_memsetRegionK_budget_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved memsetRegionSpec)) := by
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memsetGhostHookK_memsetRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_memsetRegionK_budget_withStack_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withStack (withVmPreserved memsetRegionSpec) stk)) := by
  have hcomm : memsetSpecK keep (withStack (withVmPreserved memsetRegionSpec) stk) =
      withStack (memsetSpecK keep (withVmPreserved memsetRegionSpec)) stk := by
    unfold memsetSpecK withStack
    congr 1; funext x s; exact (sepConj_assoc _ _ _).symm
  rw [hcomm]
  exact hookOk_withStack
    (memsetGhostHookK_memsetRegionK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHookK_memsetRegionK_budget_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withStack (withVmPreserved memsetRegionSpec) stk).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_memsetRegionK_budget_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_sessionMemsetRegionBudgetK_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep sessionMemsetRegionBudgetSpec) := by
  rw [← memsetSpecK_sessionMemsetRegionBudget]
  exact hookOk_withVmPreserved
    (memsetGhostHookK_sessionMemsetRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withStack sessionMemsetRegionBudgetSpec stk)) := by
  have hcomm : memsetSpecK keep (withStack sessionMemsetRegionBudgetSpec stk) =
      withStack (memsetSpecK keep sessionMemsetRegionBudgetSpec) stk := by
    unfold memsetSpecK withStack
    congr 1; funext x s; exact (sepConj_assoc _ _ _).symm
  rw [hcomm]
  exact hookOk_withStack
    (memsetGhostHookK_sessionMemsetRegionBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_keepsFs_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withStack sessionMemsetRegionBudgetSpec stk).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_sessionMemsetRegionBudgetK_withStack_ok
    hsvc_real hsvc_sub hreal_no hsub_no hwords stk).keepsFs
    (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_memsetRegionCliK_ok :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep memsetRegionCliSpec) :=
  hookOk_withOomPoolPreserved
    (memsetGhostHookK_memsetRegionK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (memsetGhostHookK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_libcMemsetCliK_ok (stk : Nat := 4096) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (libcMemsetCliSpec stk)) :=
  hookOk_withOomPoolPreserved
    (memsetGhostHookK_libcMemsetK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHookK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_session2MemsetExternK_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (session2MemsetExternSpec stk)) :=
  hookOk_session2MemsetExternK_of_master keep
    (memsetGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem memsetGhostHookK_session2MemsetExternK_keepsFs_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (session2MemsetExternSpec stk).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_session2MemsetExternK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (memsetGhostHookK_fs keep P_real P_sub entryTarget)

theorem memsetGhostHookK_session2MemsetExternK_budget_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (session2MemsetExternSpec stk))) := by
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (memsetGhostHookK_session2MemsetExternK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (memsetGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem memsetGhostHookK_session2MemsetExternK_budget_keepsFs_ok (stk : Nat := 16384) :
    HookOk (memsetGhostHookK keep P_real P_sub entryTarget)
      (memsetSpecK keep (withVmPreserved (session2MemsetExternSpec stk)).keepsFs) := by
  rw [← memsetSpecK_keepsFs]
  exact (memsetGhostHookK_session2MemsetExternK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (memsetGhostHookK_fs keep P_real P_sub entryTarget)

end GenericHookOkSuite

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
