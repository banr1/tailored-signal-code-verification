/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Heap.IfaceBudget
import ProofLib.Process.OracleEq

/-!
# Ghost `memrchr` Hook & Consumer `HookOk` Suite (`HooksDehook.MemrchrGhost`)

Card **R2-b** (`core::slice::memchr::memrchr` ghost hook + Route `β′` `withLsRet` + plain + `K`
consumer suite, mirroring `HooksDehook.BcmpGhost`):

1. **Ghost `memrchr` hooks (`memrchrGhostFnLs`, `memrchrGhostFn`, `memrchrGhostFnK`) with parametric `keepR`:**
   - `memrchrGhostFnLs [LibsignalPlacement] keepR P_real P_sub entry` (**Route `β′` primary**): wraps
     `withLsRet masterMemrchrSpec` via `linkedCallHook` with the `W`-independent fallback `memrchrHook`.
     Because `memrchr` is a non-leaf (`stp x29, x30, [sp, #-16]!`), `withLsRet` records
     `LsRetAddr624 (s.readReg64 .lr)` in `ActiveRealPre`, discharging `keepR (u.readReg64 .lr) = false`
     from `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false` (`LinkedCallHookLs`).
   - `memrchrGhostFn keepR P_real P_sub entry`: raw plain hook wrapping `masterMemrchrSpec`.
   - `memrchrGhostFnK keepR P_real P_sub entry`: placement-free `K` hook wrapping
     `memrchrSpecK keepR masterMemrchrSpec` (also lifts to `withLsRet` under `hKeep`).
2. **Variant (i) — zero panic externs, no K4 needed:**
   `P_sub := pureWordsProg entry coreMemrchrWords` (`65` words = `260` B) has `externAt? pc = none`
   and never fetches the two `bl slice_index_fail` panic blocks at `+0x104` / `+0x118` under
   `masterMemrchrSpec.pre` (`bs.length < 2 ^ 64`).
3. **Pointwise `VmPreserved`, `OomPreserved ∧ PoolPreserved`, `fs`, `HookFsTraced`, `oracle`, `trace`:**
   Established across all three `linkedCallHook` branches for `memrchrGhostFnLs`, `memrchrGhostFn`,
   and `memrchrGhostFnK` via `MemrchrCode.stdMemrchrSpec` + `StepsUntil.deterministic`.
4. **Bounded-`stk` (`∀ stk, 16 ≤ stk → stk ≤ 2 ^ 64 → …`) + `extHookStack` consumer `HookOk` suite:**
   Covers `MainHops.memrchrSpec stk`, `CalleesRO.memrchrSpecRO stk`, `Memrchr.cliMemrchrSpec stk`,
   and `CliExt.memrchrSpec` in Route `β′` (`withLsRet`), plain, and `K` forms across `keepsFs`,
   `withVmPreserved`, and `withAlloc A lim`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.Musl (memcpySrc)
open VerifiedLibraries.RustStd (lastIndexOf)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (memrchrHook)
open CryptoVerification.SignalSession.Cli.MainHops (memrchrIdx)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FdsHiFrame OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr (cliMemrchrSpec cliMemrchrSpec_extHookStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords lastIndexOf_eq_memrchrIdx)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrHook_vmPreserved memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
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
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  withLsRet extract_withLsRet intro_withLsRet subroutine_ok_withLsRet hookOk_withLsRet
  withLsRet_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs (
  linkedCallHook_lsRetAddr624_of_noException
  linkedCallHook_keepLr_false_of_noException
  linkedCallHook_withLsRet_of_not_lsRetAddr624
  specStripSInvariant_withLsRet
  specPreservesFsTrace_withLsRet
  linkedCallHook_withLsRet_ok
  hookOk_withLsRet_map_frame_pureAbort
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  memsetSpecK pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode (
  masterMemrchrSpec stdMemrchrSpec memrchrSpecK
  specStripSInvariant_masterMemrchr specStripSInvariant_masterMemrchrK
  pureWordsProg_memrchr_hasWords
  subroutine_ok_stdMemrchr_of_hasWords
  subroutine_ok_masterMemrchr_of_hasWords
  subroutine_ok_masterMemrchrK_of_hasWords
  hookMemrchr_masterMemrchr_ok hookMemrchr_masterMemrchrK_ok
  hookOk_memrchrSpecK_of_plain
  hookOk_mainHopsMemrchr_of_master hookOk_mainHopsMemrchrK_of_master
  hookOk_mainHopsMemrchrVm_of_master hookOk_mainHopsMemrchrVmK_of_master
  hookOk_cliMemrchr_of_master hookOk_cliMemrchrK_of_master
  hookOk_cliMemrchrVm_of_master hookOk_cliMemrchrVmK_of_master
  hookOk_cliExtMemrchr_of_master hookOk_cliExtMemrchrK_of_master
  hookOk_cliExtMemrchrVm_of_master hookOk_cliExtMemrchrVmK_of_master
  hookOk_cliExtMemrchr_keepsFs_of_master
  hookOk_memrchrRO_of_master hookOk_memrchrROK_of_master
  hookOk_memrchrROVm_of_master hookOk_memrchrROVmK_of_master
)

/-! ## 0. Commutation of `memrchrSpecK` and `withLsRet` with `WithAlloc.withAlloc` -/

/-- `memrchrSpecK keepR` commutes with `withAlloc A lim` by `sepConj_assoc`. -/
theorem memrchrSpecK_withAlloc (keepR : BitVec 64 → Bool) {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    memrchrSpecK keepR (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (memrchrSpecK keepR spec) := by
  unfold memrchrSpecK memsetSpecK withAlloc
  congr 1
  funext ⟨x, st⟩ s
  exact (sepConj_assoc _ _ _).symm

/-- `memrchrSpecK keepR` commutes definitionally (`rfl`) with `withVmPreserved`. -/
theorem memrchrSpecK_withVmPreserved (keepR : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    memrchrSpecK keepR (withVmPreserved spec) =
      withVmPreserved (memrchrSpecK keepR spec) := rfl

/-- `withLsRet` commutes with `withAlloc A lim` by `sepConj_assoc`. -/
theorem withLsRet_withAlloc [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (withLsRet spec) := by
  unfold withLsRet withAlloc
  congr 1
  funext ⟨x, st⟩ s
  exact (sepConj_assoc _ _ _).symm

/-! ## 1. Ghost `memrchr` Hook Definitions (`memrchrGhostFnLs`, `memrchrGhostFn`, `memrchrGhostFnK`) -/

/-- **Route `β′` primary ghost `memrchr` hook (`[LibsignalPlacement]`):** wraps
    `withLsRet masterMemrchrSpec` via `linkedCallHook` with W-free fallback `memrchrHook`. -/
@[expose] noncomputable def memrchrGhostFnLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry (withLsRet masterMemrchrSpec) memrchrHook

/-- Plain ghost `memrchr` hook wrapping `masterMemrchrSpec` via `linkedCallHook` with fallback
    `memrchrHook`. -/
@[expose] noncomputable def memrchrGhostFn
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry masterMemrchrSpec memrchrHook

/-- Placement-free `K`-narrowed ghost `memrchr` hook wrapping
    `memrchrSpecK keepR masterMemrchrSpec` via `linkedCallHook` with fallback `memrchrHook`. -/
@[expose] noncomputable def memrchrGhostFnK
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    State → State :=
  linkedCallHook keepR P_real P_sub entry (memrchrSpecK keepR masterMemrchrSpec) memrchrHook

/-- Concrete `P_sub := pureWordsProg entry coreMemrchrWords` (`65` w / `260` B) specialization of
    `memrchrGhostFnLs` (`REV-MRO` card-c note). -/
noncomputable abbrev memrchrGhostPureLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  memrchrGhostFnLs keepR P_real (pureWordsProg entry coreMemrchrWords) entry

/-- Concrete `P_sub := pureWordsProg entry coreMemrchrWords` specialization of `memrchrGhostFn`. -/
noncomputable abbrev memrchrGhostPure
    (keepR : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  memrchrGhostFn keepR P_real (pureWordsProg entry coreMemrchrWords) entry

/-- Concrete `P_sub := pureWordsProg entry coreMemrchrWords` specialization of `memrchrGhostFnK`. -/
noncomputable abbrev memrchrGhostPureK
    (keepR : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  memrchrGhostFnK keepR P_real (pureWordsProg entry coreMemrchrWords) entry

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, `setPC` Invariance & Fallback Lemmas -/

theorem specStripSInvariant_masterMemrchrLs [LibsignalPlacement] (keepR : BitVec 64 → Bool) :
    SpecStripSInvariant keepR (withLsRet masterMemrchrSpec) :=
  specStripSInvariant_withLsRet (specStripSInvariant_masterMemrchr keepR)

theorem specPreservesFsTrace_masterMemrchr :
    SpecPreservesFsTrace masterMemrchrSpec := by
  intro ⟨ro, c, p, bs⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterMemrchrSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hst := hpost.1.2
    have hfs : sf.fs = s0.fs := hst.1
    have htr : sf.trace = s0.trace := hst.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [masterMemrchrSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [masterMemrchrSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [masterMemrchrSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem specPreservesFsTrace_masterMemrchrLs [LibsignalPlacement] :
    SpecPreservesFsTrace (withLsRet masterMemrchrSpec) :=
  specPreservesFsTrace_withLsRet specPreservesFsTrace_masterMemrchr

theorem specPreservesFsTrace_masterMemrchrK (keepR : BitVec 64 → Bool) :
    SpecPreservesFsTrace (memrchrSpecK keepR masterMemrchrSpec) :=
  specPreservesFsTrace_masterMemrchr

theorem masterMemrchr_pre_setPC
    (x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) (s : State) (pc : BitVec 64) :
    masterMemrchrSpec.pre x (s.setPC pc) = masterMemrchrSpec.pre x s := by
  rcases x with ⟨_, _, _, _⟩
  cases s; rfl

theorem masterMemrchrK_pre_setPC (keepR : BitVec 64 → Bool)
    (x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) (s : State) (pc : BitVec 64) :
    (memrchrSpecK keepR masterMemrchrSpec).pre x (s.setPC pc) =
      (memrchrSpecK keepR masterMemrchrSpec).pre x s := by
  rcases x with ⟨_, _, _, _⟩
  cases s; rfl

theorem masterMemrchr_outcome_setPC
    (x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterMemrchrSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterMemrchrSpec x R s0 sf := by
  rcases x with ⟨_, _, _, _⟩
  cases s0; cases sf; exact h

theorem masterMemrchrK_outcome_setPC (keepR : BitVec 64 → Bool)
    (x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (memrchrSpecK keepR masterMemrchrSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (memrchrSpecK keepR masterMemrchrSpec) x R s0 sf := by
  rcases x with ⟨_, _, _, _⟩
  cases s0; cases sf; exact h

private theorem memrchrHook_cases (s0 : State) :
    memrchrHook s0 = CryptoVerification.SignalSession.unmodelled "memrchr: unreadable bytes" s0 ∨
    (∃ i, memrchrHook s0 =
      retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s0) ∨
    memrchrHook s0 = retHook (fun s => s.writeReg64 .x0 0#64) s0 := by
  have heq : memrchrHook s0 =
      (if (!s0.mem.canRead (s0.readReg64 .x1) (s0.readReg64 .x2).toNat) = true then
        CryptoVerification.SignalSession.unmodelled "memrchr: unreadable bytes" s0
      else
        match ((List.range (s0.mem.readBytes (s0.readReg64 .x1) (s0.readReg64 .x2).toNat).length).filter
          fun i => (s0.mem.readBytes (s0.readReg64 .x1) (s0.readReg64 .x2).toNat)[i]? ==
            some ((s0.readReg64 .x0).setWidth 8)).getLast? with
        | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s0
        | none => retHook (fun s => s.writeReg64 .x0 0#64) s0) := rfl
  rw [heq]
  split
  · exact Or.inl rfl
  · split
    · rename_i i _
      exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr rfl)

theorem keepFsTrace_memrchrHook_eq (s0 : State) :
    keepFsTrace memrchrHook s0 = memrchrHook s0 := by
  have hcases := memrchrHook_cases s0
  unfold keepFsTrace
  rcases hcases with h | ⟨i, h⟩ | h <;> rw [h] <;> (cases s0; rfl)

theorem keepFsTrace_memrchrHook_master_ok :
    HookOk (keepFsTrace memrchrHook) masterMemrchrSpec := by
  have hfn : keepFsTrace memrchrHook = memrchrHook := funext keepFsTrace_memrchrHook_eq
  rw [hfn]
  exact hookMemrchr_masterMemrchr_ok

theorem keepFsTrace_memrchrHook_masterLs_ok [LibsignalPlacement] :
    HookOk (keepFsTrace memrchrHook) (withLsRet masterMemrchrSpec) :=
  hookOk_withLsRet keepFsTrace_memrchrHook_master_ok

theorem keepFsTrace_memrchrHook_masterK_ok (keepR : BitVec 64 → Bool) :
    HookOk (keepFsTrace memrchrHook) (memrchrSpecK keepR masterMemrchrSpec) := by
  have hfn : keepFsTrace memrchrHook = memrchrHook := funext keepFsTrace_memrchrHook_eq
  rw [hfn]
  exact hookMemrchr_masterMemrchrK_ok keepR

private theorem memrchrHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (memrchrHook s0) ∧ PoolPreserved s0 (memrchrHook s0) := by
  rcases memrchrHook_cases s0 with h | ⟨i, h⟩ | h <;> rw [h] <;>
    exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

private theorem memrchrHook_oracle (s0 : State) :
    (memrchrHook s0).oracle = s0.oracle := by
  rcases memrchrHook_cases s0 with h | ⟨i, h⟩ | h <;> rw [h] <;> rfl

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`fs`, `fsT`, `VmPreserved`, `OomPreserved`, `oracle`) -/

theorem memrchrGhostFnLs_fs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memrchrGhostFnLs keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry (withLsRet masterMemrchrSpec) memrchrHook s0

theorem memrchrGhostFn_fs
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memrchrGhostFn keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry masterMemrchrSpec memrchrHook s0

theorem memrchrGhostFnK_fs
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) (s0 : State) :
    (memrchrGhostFnK keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHook_fs keepR P_real P_sub entry (memrchrSpecK keepR masterMemrchrSpec) memrchrHook s0

theorem memrchrGhostFnLs_fsT [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (memrchrGhostFnLs keepR P_real P_sub entry) :=
  linkedCallHook_fsT keepR P_real P_sub entry (withLsRet masterMemrchrSpec) memrchrHook

theorem memrchrGhostFn_fsT
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (memrchrGhostFn keepR P_real P_sub entry) :=
  linkedCallHook_fsT keepR P_real P_sub entry masterMemrchrSpec memrchrHook

theorem memrchrGhostFnK_fsT
    (keepR : BitVec 64 → Bool) (P_real P_sub : Program) (entry : BitVec 64) :
    HookFsTraced IsFsC (memrchrGhostFnK keepR P_real P_sub entry) :=
  linkedCallHook_fsT keepR P_real P_sub entry (memrchrSpecK keepR masterMemrchrSpec) memrchrHook

/-- Route `β′` master `HookOk` of `memrchrGhostFnLs` for `withLsRet masterMemrchrSpec` over any
    hook-free `P_sub` holding `coreMemrchrWords` (`65` w / `260` B) at `entry`. -/
theorem memrchrGhostFnLs_masterLs_ok [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    HookOk (memrchrGhostFnLs keepR P_real P_sub entry) (withLsRet masterMemrchrSpec) :=
  linkedCallHook_withLsRet_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_withLsRet (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords))
    (specStripSInvariant_masterMemrchr keepR)
    specPreservesFsTrace_masterMemrchr
    masterMemrchr_pre_setPC
    masterMemrchr_outcome_setPC
    keepFsTrace_memrchrHook_masterLs_ok

/-- Plain master `HookOk` of `memrchrGhostFn` for `masterMemrchrSpec`. -/
theorem memrchrGhostFn_master_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    HookOk (memrchrGhostFn keepR P_real P_sub entry) masterMemrchrSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemrchr keepR)
    specPreservesFsTrace_masterMemrchr
    masterMemrchr_pre_setPC
    masterMemrchr_outcome_setPC
    keepFsTrace_memrchrHook_master_ok

/-- `K`-narrowed master `HookOk` of `memrchrGhostFnK` for `memrchrSpecK keepR masterMemrchrSpec`. -/
theorem memrchrGhostFnK_masterK_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    HookOk (memrchrGhostFnK keepR P_real P_sub entry) (memrchrSpecK keepR masterMemrchrSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemrchrK_of_hasWords keepR hsub_no hwords)
    (specStripSInvariant_masterMemrchrK keepR)
    (specPreservesFsTrace_masterMemrchrK keepR)
    (masterMemrchrK_pre_setPC keepR)
    (masterMemrchrK_outcome_setPC keepR)
    (keepFsTrace_memrchrHook_masterK_ok keepR)

/-- Bridge `HookOk f (memrchrSpecK keepR spec)` to `HookOk f (withLsRet spec)` whenever
    `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false` holds (`K3`), so `memrchrGhostFnK` also
    feeds `withLsRet` consumers directly. -/
theorem hookOk_withLsRet_of_memrchrSpecK [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {f : State → State} {spec : Spec α}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hh : HookOk f (memrchrSpecK keepR spec)) :
    HookOk f (withLsRet spec) := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hlr, hp⟩ := extract_withLsRet hpre
  have hpreK : s0.mem ⊨ (memrchrSpecK keepR spec).pre x s0 ∗ R := by
    dsimp only [memrchrSpecK, memsetSpecK]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hKeep (s0.readReg64 .lr) hlr, hp⟩
  exact hh x R s0 hrun hpreK hsp


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

private theorem subroutineStop_of_stdMemrchrOutcome
    {x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome stdMemrchrSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · dsimp only [stdMemrchrSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [stdMemrchrSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [stdMemrchrSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

private theorem activeRealRun_stdStatePreserved_and_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    {x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterMemrchrSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keepR P_real P_sub entry s0) :
    StdStatePreserved s0 (Classical.choose hReal.2.2.2) ∧
      (Classical.choose hReal.2.2.2).oracle = s0.oracle := by
  rcases x with ⟨ro, c, p, bs⟩
  let s1 := s0.setPC entry
  let s1' := stripS keepR s1
  have hs1_pre : s1.mem ⊨ stdMemrchrSpec.pre (ro, c, p, bs) s1 ∗ R := by
    cases s0; exact hpreM
  have hs1'_pre : s1'.mem ⊨ stdMemrchrSpec.pre (ro, c, p, bs) s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keepR hs1_pre
    have heq : stdMemrchrSpec.pre (ro, c, p, bs) s1' = stdMemrchrSpec.pre (ro, c, p, bs) s1 := by
      dsimp only [s1']
      cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (subroutine_ok_stdMemrchr_of_hasWords hsub_no hwords)
      (ro, c, p, bs) R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_stdMemrchrOutcome hout'
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
  · dsimp only [stdMemrchrSpec] at hpost'
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
  · dsimp only [stdMemrchrSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [stdMemrchrSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [stdMemrchrSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

/-- Pointwise `VmPreserved` for Route `β′` `memrchrGhostFnLs` across all three branches
    (`ActiveRealRun`, fallback `memrchrHook`, and `.Exception`). -/
theorem memrchrGhostFnLs_vmPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    VmPreserved s0 (memrchrGhostFnLs keepR P_real P_sub entry s0) := by
  classical
  unfold memrchrGhostFnLs linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hwords hrun hsp (extract_withLsRet hpre).2 hReal).1
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_vmPreserved s0
  · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `VmPreserved` for plain `memrchrGhostFn`. -/
theorem memrchrGhostFn_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    VmPreserved s0 (memrchrGhostFn keepR P_real P_sub entry s0) := by
  classical
  unfold memrchrGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hwords hrun hsp hpre hReal).1
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_vmPreserved s0
  · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `VmPreserved` for `K`-narrowed `memrchrGhostFnK`. -/
theorem memrchrGhostFnK_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    VmPreserved s0 (memrchrGhostFnK keepR P_real P_sub entry s0) := by
  classical
  unfold memrchrGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memrchrSpecK, memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hwords hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_vmPreserved s0
  · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memrchrGhostFnLs`. -/
theorem memrchrGhostFnLs_oomPoolPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    OomPreserved s0 (memrchrGhostFnLs keepR P_real P_sub entry s0) ∧
      PoolPreserved s0 (memrchrGhostFnLs keepR P_real P_sub entry s0) := by
  classical
  unfold memrchrGhostFnLs linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hwords hrun hsp (extract_withLsRet hpre).2 hReal).1
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_oomPoolPreserved s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memrchrGhostFn`. -/
theorem memrchrGhostFn_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    OomPreserved s0 (memrchrGhostFn keepR P_real P_sub entry s0) ∧
      PoolPreserved s0 (memrchrGhostFn keepR P_real P_sub entry s0) := by
  classical
  unfold memrchrGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hwords hrun hsp hpre hReal).1
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_oomPoolPreserved s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `memrchrGhostFnK`. -/
theorem memrchrGhostFnK_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    OomPreserved s0 (memrchrGhostFnK keepR P_real P_sub entry s0) ∧
      PoolPreserved s0 (memrchrGhostFnK keepR P_real P_sub entry s0) := by
  classical
  unfold memrchrGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memrchrSpecK, memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_stdStatePreserved
        (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
          hwords hrun hsp hpre.2 hReal).1
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_oomPoolPreserved s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `.oracle = s0.oracle` for `memrchrGhostFnLs`. -/
theorem memrchrGhostFnLs_oracle [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    (memrchrGhostFnLs keepR P_real P_sub entry s0).oracle = s0.oracle := by
  classical
  unfold memrchrGhostFnLs linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        hwords hrun hsp (extract_withLsRet hpre).2 hReal).2
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_oracle s0
  · rfl

/-- Pointwise `.oracle = s0.oracle` for `memrchrGhostFn`. -/
theorem memrchrGhostFn_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    (memrchrGhostFn keepR P_real P_sub entry s0).oracle = s0.oracle := by
  classical
  unfold memrchrGhostFn linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        hwords hrun hsp hpre hReal).2
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_oracle s0
  · rfl

/-- Pointwise `.oracle = s0.oracle` for `memrchrGhostFnK`. -/
theorem memrchrGhostFnK_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    (memrchrGhostFnK keepR P_real P_sub entry s0).oracle = s0.oracle := by
  classical
  unfold memrchrGhostFnK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [memrchrSpecK, memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_stdStatePreserved_and_oracle hsvc_real hsvc_sub hreal_no hsub_no
        hwords hrun hsp hpre.2 hReal).2
    · rw [keepFsTrace_memrchrHook_eq]
      exact memrchrHook_oracle s0
  · rfl

theorem memrchrGhostFnLs_trace [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    (memrchrGhostFnLs keepR P_real P_sub entry s0).trace = s0.trace :=
  (memrchrGhostFnLs_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords s0).1.2.1

theorem memrchrGhostFn_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    (memrchrGhostFn keepR P_real P_sub entry s0).trace = s0.trace :=
  (memrchrGhostFn_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords s0).1.2.1

theorem memrchrGhostFnK_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords)
    (s0 : State) :
    (memrchrGhostFnK keepR P_real P_sub entry s0).trace = s0.trace :=
  (memrchrGhostFnK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords s0).1.2.1

/-- Along any non-`.Exception` call step of `memrchrGhostFnLs`, `LsRetAddr624 (u.readReg64 .lr)`
    holds (`LinkedCallHookLs`). -/
theorem memrchrGhostFnLs_lsRetAddr624_of_noException [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {u : State}
    (hnoex : ∀ msg, (memrchrGhostFnLs keepR P_real P_sub entry u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  linkedCallHook_lsRetAddr624_of_noException hnoex

/-- Route `β′` `lr ∉ keepR` extractor: along any non-`.Exception` call step of `memrchrGhostFnLs`,
    `keepR (u.readReg64 .lr) = false` follows from `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false`. -/
theorem memrchrGhostFnLs_keepLr_false_of_noException [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {u : State}
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR lr = false)
    (hnoex : ∀ msg, (memrchrGhostFnLs keepR P_real P_sub entry u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false :=
  linkedCallHook_keepLr_false_of_noException hKeep hnoex

/-- Behavior of `memrchrGhostFnLs` when `¬ LsRetAddr624 (s0.readReg64 .lr)`: transitions to
    `.Exception "ghost-hook precondition violated"`. -/
theorem memrchrGhostFnLs_of_not_lsRetAddr624 [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hnlr : ¬ LsRetAddr624 (s0.readReg64 .lr)) :
    memrchrGhostFnLs keepR P_real P_sub entry s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } :=
  linkedCallHook_withLsRet_of_not_lsRetAddr624 hnlr

/-- Along any non-`.Exception` call step of `memrchrGhostFnK`, `keepR (u.readReg64 .lr) = false`
    holds unconditionally (`K`-route `lr ∉ keepR` extractor). -/
theorem memrchrGhostFnK_keepLr_false_of_noException
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {u : State}
    (hnoex : ∀ msg, (memrchrGhostFnK keepR P_real P_sub entry u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false := by
  classical
  have hActPre : ActiveRealPre (memrchrSpecK keepR masterMemrchrSpec) u := by
    by_contra hnAct
    have hex : (memrchrGhostFnK keepR P_real P_sub entry u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold memrchrGhostFnK linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  rcases hActPre with ⟨_, _, x, R, hpre⟩
  dsimp only [memrchrSpecK, memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of plain `memrchrGhostFn` when `keepR (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterMemrchrSpec s0` holds: delegates to `memrchrHook s0`. -/
theorem memrchrGhostFn_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterMemrchrSpec s0)
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    memrchrGhostFn keepR P_real P_sub entry s0 = memrchrHook s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keepR P_real P_sub entry s0 := by
    intro hReal
    have hfalse : keepR (s0.readReg64 .lr) = false := hReal.2.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memrchrGhostFn linkedCallHook
  simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_memrchrHook_eq s0

/-- Behavior of `memrchrGhostFnK` when `keepR (s0.readReg64 .lr) = true`: transitions to
    `.Exception "ghost-hook precondition violated"`. -/
theorem memrchrGhostFnK_of_keepLr_true
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {entry : BitVec 64} {s0 : State}
    (hlr_in : keepR (s0.readReg64 .lr) = true) :
    memrchrGhostFnK keepR P_real P_sub entry s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (memrchrSpecK keepR masterMemrchrSpec) s0 := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [memrchrSpecK, memsetSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keepR (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold memrchrGhostFnK linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-! ## 4. Generic `withLsRet` Consumer `HookOk` Lifts (`16 ≤ stk ≤ 2 ^ 64`) -/

private theorem optionU64_to_memrchrMatch {c : BitVec 8} {bs : List (BitVec 8)} {sf : State}
    (hret : RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))) :
    match memrchrIdx c bs with
    | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
    | none => sf.readReg64 .x0 = 0#64 := by
  rw [lastIndexOf_eq_memrchrIdx] at hret
  cases hidx : memrchrIdx c bs with
  | none => simpa [hidx, RustAbi.optionU64] using hret
  | some i => simpa [hidx, RustAbi.optionU64] using hret

private theorem stackAt_split_frame16 {sp : BitVec 64} {stk : Nat}
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    stackAt sp stk = (stackFrameAt sp 16 ∗ memRegion (sp - BitVec.ofNat 64 stk) (stk - 16)) := by
  rw [stackAt_shrink sp stk 16 hlo hhi, stackAt_eq_stackFrameAt sp 16 (by decide), sepConj_comm]

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` to
    `HookOk f (withLsRet (MainHops.memrchrSpec stk))` for `16 ≤ stk` and `stk ≤ 2 ^ 64`. -/
theorem hookOk_withLsRet_mainHopsMemrchr_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) := by
  refine hookOk_withLsRet_map_frame_pureAbort (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ _ => ?_)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec,
      masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hlo hhi]
    sep_entail
  · dsimp only [masterMemrchrSpec,
      CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hlo hhi, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` + `VmPreserved` to
    `HookOk f (withLsRet (withVmPreserved (MainHops.memrchrSpec stk)))` (`16 ≤ stk ≤ 2 ^ 64`). -/
theorem hookOk_withLsRet_mainHopsMemrchrVm_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk f
      (withLsRet (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) :=
  hookOk_withVmPreserved (hookOk_withLsRet_mainHopsMemrchr_of_master hh stk hlo hhi) hvm

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` to
    `HookOk f (withLsRet (Memrchr.cliMemrchrSpec stk))` (`16 ≤ stk ≤ 2 ^ 64`). -/
theorem hookOk_withLsRet_cliMemrchr_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (cliMemrchrSpec stk)) := by
  refine hookOk_withLsRet_map_frame_pureAbort (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ _ => ?_)
  · dsimp only [cliMemrchrSpec, masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hlo hhi]
    sep_entail
  · dsimp only [masterMemrchrSpec, cliMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hlo hhi, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` + `VmPreserved` to
    `HookOk f (withLsRet (withVmPreserved (Memrchr.cliMemrchrSpec stk)))` (`16 ≤ stk ≤ 2 ^ 64`). -/
theorem hookOk_withLsRet_cliMemrchrVm_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (withVmPreserved (cliMemrchrSpec stk))) :=
  hookOk_withVmPreserved (hookOk_withLsRet_cliMemrchr_of_master hh stk hlo hhi) hvm

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` to
    `HookOk f (withLsRet CliExt.memrchrSpec)`. -/
theorem hookOk_withLsRet_cliExtMemrchr_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec)) :
    HookOk f (withLsRet CryptoVerification.SignalSession.CliExt.memrchrSpec) := by
  rw [← cliMemrchrSpec_extHookStack]
  exact hookOk_withLsRet_cliMemrchr_of_master hh extHookStack (by decide) (by decide)

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` + `VmPreserved` to
    `HookOk f (withLsRet (withVmPreserved CliExt.memrchrSpec))`. -/
theorem hookOk_withLsRet_cliExtMemrchrVm_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (withLsRet (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) :=
  hookOk_withVmPreserved (hookOk_withLsRet_cliExtMemrchr_of_master hh) hvm

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` to
    `HookOk f (withLsRet (keepsFs CliExt.memrchrSpec))`. -/
theorem hookOk_withLsRet_cliExtMemrchr_keepsFs_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec)) :
    HookOk f (withLsRet (keepsFs CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  refine hookOk_withLsRet_map_frame_pureAbort (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ _ => ?_)
  · dsimp only [keepsFs, CryptoVerification.SignalSession.CliExt.memrchrSpec,
      masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 (by decide : 16 ≤ extHookStack) (by decide : extHookStack ≤ 2 ^ 64)]
    sep_entail
  · dsimp only [masterMemrchrSpec, keepsFs,
      CryptoVerification.SignalSession.CliExt.memrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 (by decide : 16 ≤ extHookStack) (by decide : extHookStack ≤ 2 ^ 64),
      sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ =>
      Entails.pure_right hst.1 <|
        Entails.pure_right ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩ (by sep_entail)

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` (`ro = true`) to
    `HookOk f (withLsRet (CalleesRO.memrchrSpecRO stk))` (`16 ≤ stk ≤ 2 ^ 64`). -/
theorem hookOk_withLsRet_memrchrRO_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (memrchrSpecRO stk)) := by
  refine hookOk_withLsRet_map_frame_pureAbort (fun x => (true, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ _ => ?_)
  · dsimp only [memrchrSpecRO, masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hlo hhi]
    sep_entail
  · dsimp only [masterMemrchrSpec, memrchrSpecRO, memcpySrc, cond]
    rw [stackAt_split_frame16 hlo hhi, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- Lift `HookOk f (withLsRet masterMemrchrSpec)` + `VmPreserved` to
    `HookOk f (withLsRet (withVmPreserved (CalleesRO.memrchrSpecRO stk)))` (`16 ≤ stk ≤ 2 ^ 64`). -/
theorem hookOk_withLsRet_memrchrROVm_of_master [LibsignalPlacement] {f : State → State}
    (hh : HookOk f (withLsRet masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  hookOk_withVmPreserved (hookOk_withLsRet_memrchrRO_of_master hh stk hlo hhi) hvm

/-! ## 6. Concrete `pureWordsProg` Specializations (`P_sub` Hypotheses Discharged Unconditionally) -/

theorem memrchrGhostPureLs_masterLs_ok [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real : Program} (entry : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (memrchrGhostPureLs keepR P_real entry) (withLsRet masterMemrchrSpec) :=
  memrchrGhostFnLs_masterLs_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entry coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entry)

theorem memrchrGhostPure_master_ok
    {keepR : BitVec 64 → Bool} {P_real : Program} (entry : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (memrchrGhostPure keepR P_real entry) masterMemrchrSpec :=
  memrchrGhostFn_master_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entry coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entry)

theorem memrchrGhostPureK_masterK_ok
    {keepR : BitVec 64 → Bool} {P_real : Program} (entry : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (memrchrGhostPureK keepR P_real entry) (memrchrSpecK keepR masterMemrchrSpec) :=
  memrchrGhostFnK_masterK_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entry coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entry)

theorem memrchrGhostPureLs_vmPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real : Program} (entry : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (s0 : State) :
    VmPreserved s0 (memrchrGhostPureLs keepR P_real entry s0) :=
  memrchrGhostFnLs_vmPreserved hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entry coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entry) s0

theorem memrchrGhostPure_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real : Program} (entry : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (s0 : State) :
    VmPreserved s0 (memrchrGhostPure keepR P_real entry s0) :=
  memrchrGhostFn_vmPreserved hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entry coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entry) s0

theorem memrchrGhostPureK_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real : Program} (entry : BitVec 64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (s0 : State) :
    VmPreserved s0 (memrchrGhostPureK keepR P_real entry s0) :=
  memrchrGhostFnK_vmPreserved hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entry coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords entry) s0

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost
