/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Heap.IfaceBudget
import ProofLib.Process.OracleEq

/-!
# Ghost `bcmp` Hook & Consumer `HookOk` Suite (`HooksDehook.BcmpGhost`)

Card **L1-b** (`bcmp` ghost hook + C11 §8.1 obligations, mirroring `HooksDehook.MemsetGhost`,
`HooksDehook.MemcpyGhost`, and `HooksDehook.MemcpyGhostK`):

1. **Ghost `bcmp` hooks (`bcmpGhostFn`, `bcmpGhostFnK`) with parametric `keepR`:**
   - `bcmpGhostFn keepR P_real P_sub entry`: wraps `masterBcmpSpec` via `linkedCallHook` with the
     fixed `W`-independent fallback `hookBcmpFallback := cliBcmpHook canonicalBcmp` from `BcmpCode`
     (fixed before `∀ W : CliHooks`, matching `CliGhostHooks.extra` and `GhostRowReplayOn`).
   - `bcmpGhostFnK keepR P_real P_sub entry`: wraps the `K`-narrowed contract
     `bcmpSpecK keepR masterBcmpSpec` via `linkedCallHook` with fallback `hookBcmpFallback`.
   - `keepR : BitVec 64 → Bool` stays a parameter throughout; per GK6c there is no trusted
     placed-library entry for libc strings (code identity comes from untrusted card `a2` + `K3(b)`
     at the C2 cutover).
2. **Unconditional & 56 B contiguous-hull state / trace / VM preservation (C11 §8.1 (1)–(2)):**
   - Unconditional (no `hasWords` needed): `bcmpGhostFn_fs`, `bcmpGhostFnK_fs`
     (`∀ s, (bcmpGhostFn … s).fs = s.fs`), and `bcmpGhostFn_fsT`, `bcmpGhostFnK_fsT`
     (`HookFsTraced IsFsC (bcmpGhostFn …)`).
   - Over the single-`P_sub` 56 B contiguous `memcmp ++ bcmp` hull `bcmpHullWords m resolve` at
     entry `m + memcmpByteLen` (`= m + 52#64`): `VmPreserved` (recovered across `stripS keepR` via
     `BcmpCode.stdBcmpSpec`), `OomPreserved ∧ PoolPreserved`, `.oracle = s.oracle`, and
     `.trace = s.trace` for both `bcmpGhostFn` and `bcmpGhostFnK`, witnessed concretely on
     `pureWordsProg m (bcmpHullWords m)`.
3. **Complete consumer `HookOk` suite (C11 §8.1 (3)):**
   Lifts `bcmpGhostFn_master_ok` and `bcmpGhostFnK_masterK_ok` through `BcmpCode` §4 combinators to
   all four `bcmp` consumer contracts (`DirSpecs.cliBcmpSpec`, `CliExt.bcmpSpec` /
   `cliBcmpStackSpec stk`, `HooksE.bcmpVregsSpec`, `HooksE.e2eBcmpSpec`), in plain, `.keepsFs`,
   `withVmPreserved` (`CommonBudget`), and `withAlloc (M := M) A lim` forms, plus all `K` forms.
4. **C11 Module A (`GhostRowSpecOk`) bundling preview (§5 comment):**
   `GhostRowSpecOk` belongs to C11's `ExtraGhostSpecs.lean` (not landed yet) and is intentionally
   not defined here; §5 records the exact bundling term for `bcmpGhost_rowSpecOk`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli (CliBcmpCall cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (bcmpSpec)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec e2eBcmpSpec)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FdsHiFrame OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp (cliBcmpStackSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
  ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (
  masterBcmpSpec stdBcmpSpec bcmpSpecK
  memcmpByteLen bcmpHullWords
  pureWordsProg_bcmpHull_hasWords pureWordsProg_externAt_none
  subroutine_ok_hull_stdBcmp_of_hasWords
  subroutine_ok_hull_masterBcmp_of_hasWords
  subroutine_ok_hull_masterBcmpK_of_hasWords
  hookBcmpFallback
  hookBcmpFallback_masterBcmp_ok hookBcmpFallback_masterBcmpK_ok
  hookBcmpFallback_vmPreserved
  hookOk_bcmpSpecK_of_plain
  hookOk_dirCliBcmp_of_master hookOk_dirCliBcmpK_of_master
  hookOk_cliBcmpStack_of_master hookOk_cliBcmpStackK_of_master
  hookOk_cliExtBcmp_of_master hookOk_cliExtBcmpK_of_master
  hookOk_bcmpVregs_of_master hookOk_bcmpVregsK_of_master
  hookOk_e2eBcmp_of_master hookOk_e2eBcmpK_of_master
  hookOk_dirCliBcmp_vmPreserved_of_master hookOk_dirCliBcmpK_vmPreserved_of_master
  hookOk_cliBcmpStack_vmPreserved_of_master hookOk_cliBcmpStackK_vmPreserved_of_master
  hookOk_cliExtBcmp_vmPreserved_of_master hookOk_cliExtBcmpK_vmPreserved_of_master
  hookOk_bcmpVregsBudget_of_master hookOk_bcmpVregsBudgetK_of_master
  hookOk_e2eBcmpBudget_of_master hookOk_e2eBcmpBudgetK_of_master
  bcmpSpecK_keepsFs bcmpSpecK_withVmPreserved bcmpSpecK_withOomPoolPreserved
  bcmpSpecK_hooksEBcmpVregsBudget bcmpSpecK_hooksEE2eBcmpBudget
)

/-! ## 0. Commutation of `bcmpSpecK` with `WithAlloc.withAlloc` -/

/-- `bcmpSpecK keepR` commutes with `withAlloc A lim` by `sepConj_assoc`. -/
theorem bcmpSpecK_withAlloc (keepR : BitVec 64 → Bool) {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    bcmpSpecK keepR (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (bcmpSpecK keepR spec) := by
  unfold bcmpSpecK withAlloc
  congr 1
  funext ⟨x, st⟩ s
  exact (sepConj_assoc _ _ _).symm

/-! ## 1. Ghost `bcmp` Hook Definitions (`bcmpGhostFn`, `bcmpGhostFnK`) -/

/-- Plain ghost `bcmp` hook wrapping `masterBcmpSpec` via `linkedCallHook` with `W`-independent
    fallback `hookBcmpFallback`. Parametric in `keepR`, `P_real`, `P_sub`, and `entry`. -/
@[expose] noncomputable def bcmpGhostFn
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry masterBcmpSpec hookBcmpFallback

/-- `K`-narrowed ghost `bcmp` hook wrapping `bcmpSpecK keepR masterBcmpSpec` via `linkedCallHook`
    with fallback `hookBcmpFallback`. Outside `keepR (s.readReg64 .lr) = false` (or when
    `masterBcmpSpec.pre` fails), transitions to `.Exception` so any non-`.Exception` ghost run
    automatically witnesses `keepR (u.readReg64 .lr) = false` at every call site. -/
@[expose] noncomputable def bcmpGhostFnK
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry (bcmpSpecK keepR masterBcmpSpec) hookBcmpFallback

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, & PC Invariance -/

theorem specStripSInvariant_masterBcmp (keepR : BitVec 64 → Bool) :
    SpecStripSInvariant keepR masterBcmpSpec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterBcmpK (keepR : BitVec 64 → Bool) :
    SpecStripSInvariant keepR (bcmpSpecK keepR masterBcmpSpec) where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterBcmp :
    SpecPreservesFsTrace masterBcmpSpec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterBcmpSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hst := hpost.1.2.2
    have hfs : sf.fs = s0.fs := hst.1
    have htr : sf.trace = s0.trace := hst.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [masterBcmpSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [masterBcmpSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [masterBcmpSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem specPreservesFsTrace_masterBcmpK (keepR : BitVec 64 → Bool) :
    SpecPreservesFsTrace (bcmpSpecK keepR masterBcmpSpec) :=
  specPreservesFsTrace_masterBcmp

theorem masterBcmp_pre_setPC (x : CliBcmpCall) (s : State) (pc : BitVec 64) :
    masterBcmpSpec.pre x (s.setPC pc) = masterBcmpSpec.pre x s := by
  cases s; rfl

theorem masterBcmpK_pre_setPC (keepR : BitVec 64 → Bool)
    (x : CliBcmpCall) (s : State) (pc : BitVec 64) :
    (bcmpSpecK keepR masterBcmpSpec).pre x (s.setPC pc) =
      (bcmpSpecK keepR masterBcmpSpec).pre x s := by
  cases s; rfl

theorem masterBcmp_outcome_setPC (x : CliBcmpCall) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterBcmpSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterBcmpSpec x R s0 sf := by
  cases s0; cases sf; exact h

theorem masterBcmpK_outcome_setPC (keepR : BitVec 64 → Bool)
    (x : CliBcmpCall) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (bcmpSpecK keepR masterBcmpSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (bcmpSpecK keepR masterBcmpSpec) x R s0 sf := by
  cases s0; cases sf; exact h

theorem keepFsTrace_hookBcmpFallback_eq (s0 : State) :
    keepFsTrace hookBcmpFallback s0 = hookBcmpFallback s0 := by
  cases s0; rfl

theorem keepFsTrace_hookBcmpFallback_master_ok :
    HookOk (keepFsTrace hookBcmpFallback) masterBcmpSpec := by
  have hfn : keepFsTrace hookBcmpFallback = hookBcmpFallback :=
    funext keepFsTrace_hookBcmpFallback_eq
  rw [hfn]
  exact hookBcmpFallback_masterBcmp_ok

theorem keepFsTrace_hookBcmpFallback_masterK_ok (keepR : BitVec 64 → Bool) :
    HookOk (keepFsTrace hookBcmpFallback) (bcmpSpecK keepR masterBcmpSpec) := by
  have hfn : keepFsTrace hookBcmpFallback = hookBcmpFallback :=
    funext keepFsTrace_hookBcmpFallback_eq
  rw [hfn]
  exact hookBcmpFallback_masterBcmpK_ok keepR

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`fs`, `HookFsTraced`, `VmPreserved`, `OomPreserved`, `oracle`) -/

/-- C11 §8.1 obligation (1): `bcmpGhostFn` preserves `State.fs` unconditionally. -/
theorem bcmpGhostFn_fs
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (bcmpGhostFn keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry masterBcmpSpec hookBcmpFallback s0

/-- `K`-form C11 §8.1 obligation (1): `bcmpGhostFnK` preserves `State.fs` unconditionally. -/
theorem bcmpGhostFnK_fs
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (bcmpGhostFnK keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry (bcmpSpecK keepR masterBcmpSpec) hookBcmpFallback s0

/-- C11 §8.1 obligation (2): `bcmpGhostFn` satisfies `HookFsTraced IsFsC` unconditionally. -/
theorem bcmpGhostFn_fsT
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (bcmpGhostFn keepR P_real P_sub entry) :=
  linkedCallHook_fsT keepR P_real P_sub entry masterBcmpSpec hookBcmpFallback

/-- `K`-form C11 §8.1 obligation (2): `bcmpGhostFnK` satisfies `HookFsTraced IsFsC` unconditionally. -/
theorem bcmpGhostFnK_fsT
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (bcmpGhostFnK keepR P_real P_sub entry) :=
  linkedCallHook_fsT keepR P_real P_sub entry (bcmpSpecK keepR masterBcmpSpec) hookBcmpFallback

/-- Master `HookOk` of `bcmpGhostFn` for `masterBcmpSpec`, over a single hook-free `P_sub` holding
    the contiguous 56 B `memcmp ++ bcmp` hull `bcmpHullWords m resolve` at `m`, entered at
    `m + memcmpByteLen` (`= m + 52#64`). -/
theorem bcmpGhostFn_master_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) masterBcmpSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_hull_masterBcmp_of_hasWords hsub_no hhull hres)
    (specStripSInvariant_masterBcmp keepR)
    specPreservesFsTrace_masterBcmp
    masterBcmp_pre_setPC
    masterBcmp_outcome_setPC
    keepFsTrace_hookBcmpFallback_master_ok

/-- Master `HookOk` of `bcmpGhostFnK` for `bcmpSpecK keepR masterBcmpSpec`, over a single hook-free
    `P_sub` holding the contiguous 56 B `memcmp ++ bcmp` hull `bcmpHullWords m resolve` at `m`. -/
theorem bcmpGhostFnK_masterK_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR masterBcmpSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_hull_masterBcmpK_of_hasWords keepR hsub_no hhull hres)
    (specStripSInvariant_masterBcmpK keepR)
    (specPreservesFsTrace_masterBcmpK keepR)
    (masterBcmpK_pre_setPC keepR)
    (masterBcmpK_outcome_setPC keepR)
    (keepFsTrace_hookBcmpFallback_masterK_ok keepR)

private theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keepR : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
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
        cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_stdBcmpOutcome
    {x : CliBcmpCall} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome stdBcmpSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · dsimp only [stdBcmpSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [stdBcmpSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [stdBcmpSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

private theorem activeRealRun_stdStatePreserved_and_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m)
    {x : CliBcmpCall} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterBcmpSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keepR P_real P_sub (m + memcmpByteLen) s0) :
    StdStatePreserved s0 (Classical.choose hReal.2.2.2) ∧
      (Classical.choose hReal.2.2.2).oracle = s0.oracle := by
  let s1 := s0.setPC (m + memcmpByteLen)
  let s1' := stripS keepR s1
  have hs1_pre : s1.mem ⊨ stdBcmpSpec.pre x s1 ∗ R := by
    cases s0; exact hpreM
  have hs1'_pre : s1'.mem ⊨ stdBcmpSpec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keepR hs1_pre
    have heq : stdBcmpSpec.pre x s1' = stdBcmpSpec.pre x s1 := by
      dsimp only [s1']
      cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (subroutine_ok_hull_stdBcmp_of_hasWords hsub_no hhull hres)
      x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_stdBcmpOutcome hout'
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
  · dsimp only [stdBcmpSpec] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : StdStatePreserved s1' sf' := hpost'.1.2.2
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
  · dsimp only [stdBcmpSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [stdBcmpSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [stdBcmpSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

/-- Pointwise `VmPreserved` for `bcmpGhostFn` across all three branches (`ActiveRealRun`,
    fallback `hookBcmpFallback`, and `.Exception`). -/
theorem bcmpGhostFn_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    VmPreserved s0 (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen) s0) := by
  classical
  unfold bcmpGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hhull hres hrun hsp hpre hReal).1
    · rw [keepFsTrace_hookBcmpFallback_eq]
      exact hookBcmpFallback_vmPreserved s0
  · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `VmPreserved` for `bcmpGhostFnK` across all three branches. -/
theorem bcmpGhostFnK_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    VmPreserved s0 (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen) s0) := by
  classical
  unfold bcmpGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [bcmpSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hhull hres hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_hookBcmpFallback_eq]
      exact hookBcmpFallback_vmPreserved s0
  · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `bcmpGhostFn`. -/
theorem bcmpGhostFn_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    OomPreserved s0 (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen) s0) ∧
      PoolPreserved s0 (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen) s0) := by
  classical
  unfold bcmpGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hhull hres hrun hsp hpre hReal).1
    · rw [keepFsTrace_hookBcmpFallback_eq]
      exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `bcmpGhostFnK`. -/
theorem bcmpGhostFnK_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    OomPreserved s0 (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen) s0) ∧
      PoolPreserved s0 (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen) s0) := by
  classical
  unfold bcmpGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [bcmpSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hhull hres hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_hookBcmpFallback_eq]
      exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `.oracle = s0.oracle` for `bcmpGhostFn`. -/
theorem bcmpGhostFn_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen) s0).oracle = s0.oracle := by
  classical
  unfold bcmpGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        hhull hres hrun hsp hpre hReal).2
    · rw [keepFsTrace_hookBcmpFallback_eq]
      cases s0; rfl
  · rfl

/-- Pointwise `.oracle = s0.oracle` for `bcmpGhostFnK`. -/
theorem bcmpGhostFnK_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen) s0).oracle = s0.oracle := by
  classical
  unfold bcmpGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [bcmpSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        hhull hres hrun hsp hpre.2 hReal).2
    · rw [keepFsTrace_hookBcmpFallback_eq]
      cases s0; rfl
  · rfl

/-- Pointwise `.trace = s0.trace` for `bcmpGhostFn`. -/
theorem bcmpGhostFn_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen) s0).trace = s0.trace :=
  (bcmpGhostFn_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0).1.2.1

/-- Pointwise `.trace = s0.trace` for `bcmpGhostFnK`. -/
theorem bcmpGhostFnK_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl)
    (s0 : State) :
    (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen) s0).trace = s0.trace :=
  (bcmpGhostFnK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres s0).1.2.1

/-- Along any non-`.Exception` call step of `bcmpGhostFnK`, `keepR (u.readReg64 .lr) = false`
    holds automatically (`K`-route `lr ∉ keepR` extractor). -/
theorem bcmpGhostFnK_keepLr_false_of_noException
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {u : State}
    (hnoex : ∀ msg, (bcmpGhostFnK keepR P_real P_sub entry u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false := by
  classical
  have hActPre : ActiveRealPre (bcmpSpecK keepR masterBcmpSpec) u := by
    by_contra hnAct
    have hex : (bcmpGhostFnK keepR P_real P_sub entry u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold bcmpGhostFnK linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  rcases hActPre with ⟨_, _, x, R, hpre⟩
  dsimp only [bcmpSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of plain `bcmpGhostFn` when `keepR (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterBcmpSpec s0` holds: `ActiveRealRun` is false, so `linkedCallHook`
    delegates to `keepFsTrace hookBcmpFallback s0 = hookBcmpFallback s0`. -/
theorem bcmpGhostFn_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterBcmpSpec s0)
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    bcmpGhostFn keepR P_real P_sub entry s0 = hookBcmpFallback s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keepR P_real P_sub entry s0 := by
    intro hReal
    have hfalse : keepR (s0.readReg64 .lr) = false := hReal.2.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold bcmpGhostFn linkedCallHook
  simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_hookBcmpFallback_eq s0

/-- Behavior of `K`-narrowed `bcmpGhostFnK` when `keepR (s0.readReg64 .lr) = true`:
    `ActiveRealPre (bcmpSpecK keepR masterBcmpSpec) s0` is false regardless of memory contents, so
    `linkedCallHook` transitions to `.Exception "ghost-hook precondition violated"`. -/
theorem bcmpGhostFnK_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    bcmpGhostFnK keepR P_real P_sub entry s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (bcmpSpecK keepR masterBcmpSpec) s0 := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [bcmpSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keepR (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold bcmpGhostFnK linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-! ## 4. Complete Consumer `HookOk` Suite (Plain, `keepsFs`, `withVmPreserved`, `withAlloc`, & `K`) -/

section GenericHookOkSuite

variable {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
variable {m : BitVec 64} {resolve : String → BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
variable (hres : resolve "memcmp" = m)

include hsvc_real hsvc_sub hreal_no hsub_no hhull hres

-- 4.1 Plain contracts on `bcmpGhostFn` (all 4 consumer specs + stack-parametric `cliBcmpStackSpec`):

theorem bcmpGhostFn_dirCliBcmp_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) cliBcmpSpec :=
  hookOk_dirCliBcmp_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_cliBcmpStack_ok (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) (cliBcmpStackSpec stk) :=
  hookOk_cliBcmpStack_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem bcmpGhostFn_cliExtBcmp_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) bcmpSpec :=
  hookOk_cliExtBcmp_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_bcmpVregs_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) bcmpVregsSpec :=
  hookOk_bcmpVregs_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_e2eBcmp_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) e2eBcmpSpec :=
  hookOk_e2eBcmp_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

-- 4.2 Budget / `withVmPreserved` variants on `bcmpGhostFn` (through `BcmpCode` §4 combinators):

theorem bcmpGhostFn_dirCliBcmp_budget_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) (withVmPreserved cliBcmpSpec) :=
  hookOk_dirCliBcmp_vmPreserved_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_cliBcmpStack_budget_ok (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withVmPreserved (cliBcmpStackSpec stk)) :=
  hookOk_cliBcmpStack_vmPreserved_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem bcmpGhostFn_cliExtBcmp_budget_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) (withVmPreserved bcmpSpec) :=
  hookOk_cliExtBcmp_vmPreserved_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_bcmpVregs_budget_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec :=
  hookOk_bcmpVregsBudget_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_e2eBcmp_budget_ok :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec :=
  hookOk_e2eBcmpBudget_of_master
    (bcmpGhostFn_master_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFn_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

-- 4.3 Pool-framed `withAlloc (M := M) A lim` variants on `bcmpGhostFn` (all 4 consumer specs):

theorem bcmpGhostFn_dirCliBcmp_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim cliBcmpSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpGhostFn_dirCliBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_dirCliBcmp_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim (withVmPreserved cliBcmpSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (bcmpGhostFn_dirCliBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_cliBcmpStack_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim (cliBcmpStackSpec stk)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpGhostFn_cliBcmpStack_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres stk)

theorem bcmpGhostFn_cliBcmpStack_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim (withVmPreserved (cliBcmpStackSpec stk))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (bcmpGhostFn_cliBcmpStack_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres stk)

theorem bcmpGhostFn_cliExtBcmp_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim bcmpSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpGhostFn_cliExtBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_cliExtBcmp_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim (withVmPreserved bcmpSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (bcmpGhostFn_cliExtBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_bcmpVregs_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim bcmpVregsSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpGhostFn_bcmpVregs_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_bcmpVregs_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec) :=
  hookOk_withAlloc_withVmPreserved A lim
    (bcmpGhostFn_bcmpVregs_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_e2eBcmp_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim e2eBcmpSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpGhostFn_e2eBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFn_e2eBcmp_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen))
      (withAlloc (M := M) A lim LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec) :=
  hookOk_withAlloc_withVmPreserved A lim
    (bcmpGhostFn_e2eBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

-- 4.4 Generic `.keepsFs`, `withOomPoolPreserved`, `withExecFrozen`, & `bcmpSpecK` corollaries:

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem bcmpGhostFn_any_keepsFs_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (bcmpGhostFn keepR P_real P_sub entry) spec) :
    HookOk (bcmpGhostFn keepR P_real P_sub entry) spec.keepsFs :=
  hh.keepsFs (bcmpGhostFn_fs keepR P_real P_sub entry)

theorem bcmpGhostFn_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) spec) :
    HookOk (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (bcmpGhostFn_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem bcmpGhostFn_any_execFrozen_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (bcmpGhostFn keepR P_real P_sub entry) spec) :
    HookOk (bcmpGhostFn keepR P_real P_sub entry) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem bcmpGhostFn_any_bcmpSpecK_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (bcmpGhostFn keepR P_real P_sub entry) spec) :
    HookOk (bcmpGhostFn keepR P_real P_sub entry) (bcmpSpecK keepR spec) :=
  hookOk_bcmpSpecK_of_plain keepR hh

-- 4.5 `K`-narrowed (`bcmpSpecK keepR …`) contracts on `bcmpGhostFnK` (plain, `withVmPreserved`,
-- and `withAlloc A lim` across all 4 consumer specs):

theorem bcmpGhostFnK_dirCliBcmpK_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen)) (bcmpSpecK keepR cliBcmpSpec) :=
  hookOk_dirCliBcmpK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_cliBcmpStackK_ok (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (cliBcmpStackSpec stk)) :=
  hookOk_cliBcmpStackK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem bcmpGhostFnK_cliExtBcmpK_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen)) (bcmpSpecK keepR bcmpSpec) :=
  hookOk_cliExtBcmpK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_bcmpVregsK_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen)) (bcmpSpecK keepR bcmpVregsSpec) :=
  hookOk_bcmpVregsK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_e2eBcmpK_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen)) (bcmpSpecK keepR e2eBcmpSpec) :=
  hookOk_e2eBcmpK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_dirCliBcmpK_budget_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withVmPreserved cliBcmpSpec)) :=
  hookOk_dirCliBcmpK_vmPreserved_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_cliBcmpStackK_budget_ok (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withVmPreserved (cliBcmpStackSpec stk))) :=
  hookOk_cliBcmpStackK_vmPreserved_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres) stk

theorem bcmpGhostFnK_cliExtBcmpK_budget_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withVmPreserved bcmpSpec)) :=
  hookOk_cliExtBcmpK_vmPreserved_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_bcmpVregsBudgetK_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec) :=
  hookOk_bcmpVregsBudgetK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_e2eBcmpBudgetK_ok :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec) :=
  hookOk_e2eBcmpBudgetK_of_master keepR
    (bcmpGhostFnK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)
    (bcmpGhostFnK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_dirCliBcmpK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim cliBcmpSpec)) := by
  rw [bcmpSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpSpecK_withVmPreserved keepR cliBcmpSpec ▸
      bcmpGhostFnK_dirCliBcmpK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_dirCliBcmpK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim (withVmPreserved cliBcmpSpec))) := by
  rw [bcmpSpecK_withAlloc, ← bcmpSpecK_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (bcmpSpecK_withVmPreserved keepR cliBcmpSpec ▸
      bcmpGhostFnK_dirCliBcmpK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_cliBcmpStackK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim (cliBcmpStackSpec stk))) := by
  rw [bcmpSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpSpecK_withVmPreserved keepR (cliBcmpStackSpec stk) ▸
      bcmpGhostFnK_cliBcmpStackK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres stk)

theorem bcmpGhostFnK_cliBcmpStackK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := extHookStack) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim (withVmPreserved (cliBcmpStackSpec stk)))) := by
  rw [bcmpSpecK_withAlloc, ← bcmpSpecK_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (bcmpSpecK_withVmPreserved keepR (cliBcmpStackSpec stk) ▸
      bcmpGhostFnK_cliBcmpStackK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres stk)

theorem bcmpGhostFnK_cliExtBcmpK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim bcmpSpec)) := by
  rw [bcmpSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpSpecK_withVmPreserved keepR bcmpSpec ▸
      bcmpGhostFnK_cliExtBcmpK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_cliExtBcmpK_budget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim (withVmPreserved bcmpSpec))) := by
  rw [bcmpSpecK_withAlloc, ← bcmpSpecK_withVmPreserved]
  exact hookOk_withAlloc_withVmPreserved A lim
    (bcmpSpecK_withVmPreserved keepR bcmpSpec ▸
      bcmpGhostFnK_cliExtBcmpK_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_bcmpVregsK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim bcmpVregsSpec)) := by
  rw [bcmpSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpSpecK_hooksEBcmpVregsBudget keepR ▸
      bcmpGhostFnK_bcmpVregsBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_bcmpVregsBudgetK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR
        (withAlloc (M := M) A lim LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.bcmpVregsSpec)) := by
  rw [bcmpSpecK_withAlloc, ← bcmpSpecK_hooksEBcmpVregsBudget]
  exact hookOk_withAlloc_withVmPreserved A lim
    (bcmpSpecK_hooksEBcmpVregsBudget keepR ▸
      bcmpGhostFnK_bcmpVregsBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_e2eBcmpK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withAlloc (M := M) A lim e2eBcmpSpec)) := by
  rw [bcmpSpecK_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (bcmpSpecK_hooksEE2eBcmpBudget keepR ▸
      bcmpGhostFnK_e2eBcmpBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

theorem bcmpGhostFnK_e2eBcmpBudgetK_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR
        (withAlloc (M := M) A lim LibsignalBinary.Proofs.E2E.HooksE.CommonBudget.e2eBcmpSpec)) := by
  rw [bcmpSpecK_withAlloc, ← bcmpSpecK_hooksEE2eBcmpBudget]
  exact hookOk_withAlloc_withVmPreserved A lim
    (bcmpSpecK_hooksEE2eBcmpBudget keepR ▸
      bcmpGhostFnK_e2eBcmpBudgetK_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem bcmpGhostFnK_any_keepsFs_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (bcmpGhostFnK keepR P_real P_sub entry) (bcmpSpecK keepR spec)) :
    HookOk (bcmpGhostFnK keepR P_real P_sub entry) (bcmpSpecK keepR spec.keepsFs) :=
  bcmpSpecK_keepsFs keepR spec ▸ hh.keepsFs (bcmpGhostFnK_fs keepR P_real P_sub entry)

theorem bcmpGhostFnK_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen)) (bcmpSpecK keepR spec)) :
    HookOk (bcmpGhostFnK keepR P_real P_sub (m + memcmpByteLen))
      (bcmpSpecK keepR (withOomPoolPreserved spec)) :=
  bcmpSpecK_withOomPoolPreserved keepR spec ▸
    hookOk_withOomPoolPreserved hh
      (bcmpGhostFnK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hhull hres)

omit hsvc_real hsvc_sub hreal_no hsub_no hhull hres in
theorem bcmpGhostFnK_any_execFrozen_ok {α : Type} {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (bcmpGhostFnK keepR P_real P_sub entry) spec) :
    HookOk (bcmpGhostFnK keepR P_real P_sub entry) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

end GenericHookOkSuite

/-- Concrete `pureWordsProg m (bcmpHullWords m)` instantiation of `bcmpGhostFn_master_ok`
    witnessing joint satisfiability of all `P_sub` hull premises. -/
theorem bcmpGhostFn_pureHull_master_ok
    {keepR : BitVec 64 → Bool} {P_real : Program} (m : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (bcmpGhostFn keepR P_real (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen))
      masterBcmpSpec :=
  bcmpGhostFn_master_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m) rfl

/-- Concrete `pureWordsProg m (bcmpHullWords m)` instantiation of `bcmpGhostFnK_masterK_ok`. -/
theorem bcmpGhostFnK_pureHull_masterK_ok
    {keepR : BitVec 64 → Bool} {P_real : Program} (m : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (bcmpGhostFnK keepR P_real (pureWordsProg m (bcmpHullWords m)) (m + memcmpByteLen))
      (bcmpSpecK keepR masterBcmpSpec) :=
  bcmpGhostFnK_masterK_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none m (bcmpHullWords m))
    (pureWordsProg_bcmpHull_hasWords m) rfl

/-! ## 5. C11 Module A (`GhostRowSpecOk`) Bundling Preview

`GhostRowSpecOk` belongs to C11's Module A
(`LibsignalBinary/Proofs/SignalSession/Cli/Run/Slots/ExtraGhostSpecs.lean`, not landed yet) and is
intentionally **not** defined here. Once Module A lands, the three C11 §8.1 obligations proved above
bundle directly into `bcmpGhost_rowSpecOk` in 4 lines:

```lean
theorem bcmpGhost_rowSpecOk
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bcmpHullWords m resolve))
    (hres : resolve "memcmp" = m := by rfl) :
    GhostRowSpecOk M A lim "bcmp"
      (bcmpGhostFn keepR P_real P_sub (m + memcmpByteLen)) :=
  ⟨bcmpGhostFn_fs keepR P_real P_sub (m + memcmpByteLen),
   bcmpGhostFn_fsT keepR P_real P_sub (m + memcmpByteLen),
   bcmpGhostFn_dirCliBcmp_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres,
   bcmpGhostFn_dirCliBcmp_budget_withAlloc_ok hsvc_real hsvc_sub hreal_no hsub_no hhull hres A lim⟩
```
-/

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost
