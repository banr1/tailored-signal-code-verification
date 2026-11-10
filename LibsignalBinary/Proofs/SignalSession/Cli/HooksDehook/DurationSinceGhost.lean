/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Heap.IfaceBudget
import ProofLib.Process.OracleEq

/-!
# Ghost `SystemTime::duration_since` Hook & Route-β′ Consumer `HookOk` Suite (`HooksDehook.DurationSinceGhost`)

Card **R3-b** (part 1 of 2; companion replay & `W`-independent `emptyStdProg` module:
`HooksDehook.DurationSinceGhostLs`):

1. **Instruction & `.rodata.cst16` source (`timeMultiLib` blocks):**
   All verified instruction words and `.rodata.cst16` bytes originate from the engine's
   `VerifiedLibraries.RustStd.timeMultiLib`:
   - block `0`: `Timespec::sub_timespec` (`60` words = `240` B = `subTimespecByteLen`);
   - block `1`: `<std::time::SystemTime>::duration_since` (`20` words = `80` B);
   - `.rodata.cst16`: `16`-byte constant `timePlacedData0` at `mpl.ρ timeRodataCst16Sym`, placed on
     the run-side state guard `roTableGuard cst16Addr timePlacedData0` of `linkedCallHookG`
     (never in consumer `.pre`).
   (STOCK-PLAN verified `[M]` that the GNU and musl `core`/`std` copies of `sub_timespec` (`60` w),
   `duration_since` (`20` w), and the `cst16` entry are byte-identical.)
2. **Why `duration_since` needs zero panic-stub externs (`P_sub.externAt? = none`):**
   Although `timeMultiLib` block `0` ends with a cold `bl core::option::expect_failed` at
   `sub_timespec + 236` (word `59`), `masterDurationSinceSpec` and every CLI consumer
   `durationSince{Bounded,Epoch}*` contract require valid `Timespec` nanoseconds (`tv_nsec < 10^9`)
   in `.pre` and have `onPanic = ⌜False⌝`. Under `tv_nsec < 10^9`, `|t1 - t2| / 10^9 < 2^64`, so
   word `59` is never executed on any `ActiveRealPre` state (`DurationSinceHullAux`). Consequently,
   the hook-free `80`-word hull `durationSinceHullProg mpl` (`externAt? = none`) satisfies
   `subroutine_ok` directly with zero `#1344` panic-stub extern plumbing.
3. **Ghost hooks (`durationSinceGhostFn`, Route-β′ `durationSinceGhostFnLs`):**
   - `durationSinceGhostFn cst16Addr keepR P_real P_sub entry`: wraps `masterDurationSinceSpec` via
     `linkedCallHookG (roTableGuard cst16Addr timePlacedData0)` with `W`-independent fallback
     `durationSinceExactHook`.
   - `durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry`: Route-β′ `[LibsignalPlacement]`
     sibling wrapping `WithLsRet.withLsRet masterDurationSinceSpec`, so any non-`.Exception`
     evaluation witnesses `LsRetAddr624 (u.readReg64 .lr)` (discharging `keepR (u.lr) = false` via
     K3's `∀ lr, LsRetAddr624 lr → keepR lr = false`).
4. **C11 §8.1 State / VM / Trace Bundle & Consumer `HookOk` Suite:**
   - Unconditional `.fs = s.fs` and `HookFsTraced IsFsC`;
   - Over patched `sub_timespec` + `duration_since` words (and specialized to the `80`-word
     contiguous hull at `hullBase + subTimespecByteLen`): pointwise `VmPreserved` (recovered across
     `stripS keepR` via `DurationSinceCode.stdDurationSinceSpec`), `OomPreserved ∧ PoolPreserved`,
     `.oracle = s.oracle`, and `.trace = s.trace`;
   - Complete plain and Route-β′ (`withLsRet`) consumer `HookOk` suite across all bounded and epoch
     contracts (bare, `.keepsFs`, `withVmPreserved` budget, `.inImage`, `withAlloc A lim`,
     `withOomPoolPreserved`, and `withExecFrozen`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost

open Arm64 Arm64.Obj ProofLib SepProp
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.RustStd (
  timeMultiLib timePlacedData0 timeRodataCst16Sym
)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (durationSinceExactHook)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (durationSinceEpochSpec)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FdsHiFrame OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved durationSinceEpochBudgetSpec)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince (
  durationSinceEpochAtSpec durationSinceBoundedAtSpec durationSinceBoundedSpec
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm (
  durationSinceEpochAllocSpec durationSinceEpochAllocBudgetSpec
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm (
  durationSinceBoundedBudgetAtSpec durationSinceBoundedBudgetSpec
  durationSinceBoundedAllocSpec durationSinceBoundedAllocBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
  ActiveRealPre ActiveRealRun
  linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG linkedCallHookG_eq_of_guard linkedCallHookG_eq_of_not_guard
  linkedCallHookG_activeRealPre_of_noException linkedCallHookG_of_keepLr_true
  linkedCallHookG_fs linkedCallHookG_fsT
  roTableGuard roTableGuard_stripS hookOk_linkedCallHookG_roTable
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  withLsRet withLsRet_outcome_eq extract_withLsRet intro_withLsRet
  withLsRet_pre_setPC withLsRet_outcome_setPC hookOk_withLsRet
  withLsRet_frameLeft withLsRet_keepsFs withLsRet_withOomPoolPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs (
  lsRetAddr624_of_noException_via_activeRealPre keepLr_false_of_noException_via_activeRealPre
  not_activeRealPre_withLsRet_of_not_lsRetAddr624 linkedCallHook_withLsRet_of_not_lsRetAddr624
  specStripSInvariant_withLsRet specPreservesFsTrace_withLsRet subroutine_ok_withRoData_withLsRet
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode (
  DurationSinceGhost masterDurationSinceSpec stdDurationSinceSpec
  stdDurationSince_pre_eq
  specStripSInvariant_masterDurationSince specPreservesFsTrace_masterDurationSince
  masterDurationSince_pre_setPC masterDurationSince_outcome_setPC
  subTimespecPatchedWords durationSincePatchedWords durationSinceHullProg
  durationSinceHullProg_hasWords_subTimespec durationSinceHullProg_hasWords_durationSince
  durationSinceHullProg_externAt_none durationSinceHullProg_svc
  subroutine_ok_stdDurationSince_of_hasWords subroutine_ok_masterDurationSince_of_hasWords
  durationSinceExactHook_vm durationSinceExactHook_master_ok
  keepFsTrace_durationSinceExactHook_eq keepFsTrace_durationSinceExactHook_master_ok
  hookOk_linkedCallHookG_durationSince
  hookOk_durationSinceBoundedAt_keepsFs_of_master hookOk_durationSinceBoundedAt_of_master
  hookOk_durationSinceEpochAt_keepsFs_of_master hookOk_durationSinceEpochAt_of_master
  hookOk_durationSinceBounded_of_master hookOk_durationSinceBounded_keepsFs_of_master
  hookOk_durationSinceBoundedAlloc_of_master hookOk_durationSinceBoundedBudgetAt_of_master
  hookOk_durationSinceBoundedBudget_of_master hookOk_durationSinceBoundedBudget_keepsFs_of_master
  hookOk_durationSinceBoundedAllocBudget_of_master
  hookOk_durationSinceBounded_inImage_of_master hookOk_durationSinceBoundedBudget_inImage_of_master
  hookOk_durationSinceEpoch_of_master hookOk_durationSinceEpoch_keepsFs_of_master
  hookOk_durationSinceEpochAlloc_of_master hookOk_durationSinceEpochBudgetAt_of_master
  hookOk_durationSinceEpochBudget_of_master hookOk_durationSinceEpochBudget_keepsFs_of_master
  hookOk_durationSinceEpochAllocBudget_of_master
  hookOk_durationSinceEpoch_inImage_of_master hookOk_durationSinceEpochBudget_inImage_of_master
)

/-! ## 0. Named Hull Offset, `hookOk_congr`, & `withLsRet` Wrapper Commutations -/

/-- Byte length (`240` B = `60` words) of `Timespec::sub_timespec` (`timeMultiLib` block `0`), i.e.
    the entry offset of `SystemTime::duration_since` (`timeMultiLib` block `1`, `20` words = `80` B)
    inside the contiguous `80`-word (`320` B) `.text.lib2` hull `sub_timespec ++ duration_since`. -/
@[expose] def subTimespecByteLen : BitVec 64 := 240#64

/-- Transport `HookOk f` across a `Spec` equality (`REV-PILOT` N1 helper). -/
theorem hookOk_congr {α : Type} {f : State → State} {spec₁ spec₂ : Spec α}
    (heq : spec₁ = spec₂) (hh : HookOk f spec₁) :
    HookOk f spec₂ :=
  heq ▸ hh

/-- `withLsRet` commutes with `WithAlloc.withAlloc A lim` by `sepConj_assoc`. -/
theorem withLsRet_withAlloc [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (withLsRet spec) := by
  unfold withLsRet withAlloc
  congr 1
  funext ⟨x, st⟩ s
  exact (sepConj_assoc _ _ _).symm

/-- `withLsRet` commutes with `MemsetGhost.withExecFrozen` by `sepConj_left_comm`. -/
theorem withLsRet_withExecFrozen [LibsignalPlacement] {α : Type} (spec : Spec α) :
    withLsRet (withExecFrozen spec) = withExecFrozen (withLsRet spec) :=
  withLsRet_frameLeft spec (fun _ s => ⌜ExecFrozen s.mem⌝) spec.post

/-! ## 1. Ghost `duration_since` Hook Definitions (`durationSinceGhostFn`, `durationSinceGhostFnLs`) -/

/-- Plain state-guarded ghost `SystemTime::duration_since` hook wrapping `masterDurationSinceSpec`
    via `linkedCallHookG (roTableGuard cst16Addr timePlacedData0)` with `W`-independent fallback
    `durationSinceExactHook`. Parametric in `cst16Addr`, `keepR`, `P_real`, `P_sub`, and `entry`. -/
@[expose] noncomputable def durationSinceGhostFn
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry : BitVec 64) : State → State :=
  linkedCallHookG (roTableGuard cst16Addr timePlacedData0)
    keepR P_real P_sub entry masterDurationSinceSpec durationSinceExactHook

/-- Route-β′ (`[LibsignalPlacement]`) ghost `SystemTime::duration_since` hook wrapping
    `withLsRet masterDurationSinceSpec` via `linkedCallHookG (roTableGuard cst16Addr timePlacedData0)`
    with `W`-independent fallback `durationSinceExactHook`. Outside `LsRetAddr624 (s.readReg64 .lr)`
    (or when `masterDurationSinceSpec.pre` fails), transitions to `.Exception`, so any
    non-`.Exception` call step automatically witnesses `LsRetAddr624 (u.readReg64 .lr)`. -/
@[expose] noncomputable def durationSinceGhostFnLs [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry : BitVec 64) : State → State :=
  linkedCallHookG (roTableGuard cst16Addr timePlacedData0)
    keepR P_real P_sub entry (withLsRet masterDurationSinceSpec) durationSinceExactHook

/-- Concrete `80`-word contiguous hull specialization of `durationSinceGhostFn` at
    `P_sub := durationSinceHullProg mpl` and entry `hullBase + subTimespecByteLen`. -/
noncomputable abbrev durationSinceHullGhostFn
    (keepR : BitVec 64 → Bool) (P_real : Program) (mpl : MultiPlacement)
    (hullBase : BitVec 64) : State → State :=
  durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real
    (durationSinceHullProg mpl) (hullBase + subTimespecByteLen)

/-- Concrete `80`-word contiguous hull specialization of `durationSinceGhostFnLs` at
    `P_sub := durationSinceHullProg mpl` and entry `hullBase + subTimespecByteLen`. -/
noncomputable abbrev durationSinceHullGhostFnLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) (P_real : Program) (mpl : MultiPlacement)
    (hullBase : BitVec 64) : State → State :=
  durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real
    (durationSinceHullProg mpl) (hullBase + subTimespecByteLen)

/-! ## 2. Route-β′ (`withLsRet`) Side Obligations, Master `HookOk`, & `LsRetAddr624` Extractors -/

theorem specStripSInvariant_masterDurationSinceLs [LibsignalPlacement]
    (keepR : BitVec 64 → Bool) :
    SpecStripSInvariant keepR (withLsRet masterDurationSinceSpec) :=
  specStripSInvariant_withLsRet (specStripSInvariant_masterDurationSince keepR)

theorem specPreservesFsTrace_masterDurationSinceLs [LibsignalPlacement] :
    SpecPreservesFsTrace (withLsRet masterDurationSinceSpec) :=
  specPreservesFsTrace_withLsRet specPreservesFsTrace_masterDurationSince

theorem masterDurationSinceLs_pre_setPC [LibsignalPlacement]
    (x : DurationSinceGhost) (s : State) (pc : BitVec 64) :
    (withLsRet masterDurationSinceSpec).pre x (s.setPC pc) =
      (withLsRet masterDurationSinceSpec).pre x s :=
  withLsRet_pre_setPC masterDurationSince_pre_setPC x s pc

theorem masterDurationSinceLs_outcome_setPC [LibsignalPlacement]
    (x : DurationSinceGhost) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (withLsRet masterDurationSinceSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLsRet masterDurationSinceSpec) x R s0 sf :=
  withLsRet_outcome_setPC masterDurationSince_outcome_setPC x R s0 sf pc h

theorem keepFsTrace_durationSinceExactHook_masterLs_ok [LibsignalPlacement] :
    HookOk (keepFsTrace durationSinceExactHook) (withLsRet masterDurationSinceSpec) :=
  hookOk_withLsRet keepFsTrace_durationSinceExactHook_master_ok

theorem subroutine_ok_masterDurationSinceLs_of_hasWords [LibsignalPlacement]
    {P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl)) :
    subroutine_ok P_sub (mpl.base 1)
      (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (withLsRet masterDurationSinceSpec)) :=
  subroutine_ok_withRoData_withLsRet
    (subroutine_ok_masterDurationSince_of_hasWords hpl hsvc hsub_no hw0 hw1)

theorem durationSinceHullProg_masterDurationSinceLs_ok [LibsignalPlacement]
    {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl)
    (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen) :
    subroutine_ok (durationSinceHullProg mpl) (hullBase + subTimespecByteLen)
      (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (withLsRet masterDurationSinceSpec)) := by
  rw [← hb1]
  refine subroutine_ok_masterDurationSinceLs_of_hasWords hpl
    (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
  rw [hb1, ← hb0]
  exact durationSinceHullProg_hasWords_durationSince mpl

/-- Master `HookOk` of `durationSinceGhostFn` for `masterDurationSinceSpec` over any hook-free
    `P_sub` holding the relocation-patched `timeMultiLib` block `0` and block `1` words. -/
theorem durationSinceGhostFn_master_ok
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl)) :
    HookOk (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1))
      masterDurationSinceSpec :=
  hookOk_linkedCallHookG_durationSince hpl hsvc_real hsvc_sub hreal_no hsub_no hw0 hw1

/-- Route-β′ master `HookOk` of `durationSinceGhostFnLs` for `withLsRet masterDurationSinceSpec`
    over any hook-free `P_sub` holding the relocation-patched `timeMultiLib` block `0` and `1`
    words. -/
theorem durationSinceGhostFnLs_masterLs_ok [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl)) :
    HookOk (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1))
      (withLsRet masterDurationSinceSpec) :=
  hookOk_linkedCallHookG_roTable hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterDurationSinceLs_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
    (specStripSInvariant_masterDurationSinceLs keepR)
    specPreservesFsTrace_masterDurationSinceLs
    masterDurationSinceLs_pre_setPC
    masterDurationSinceLs_outcome_setPC
    keepFsTrace_durationSinceExactHook_masterLs_ok

/-- Concrete `80`-word contiguous hull master `HookOk` for `durationSinceHullGhostFn`. -/
theorem durationSinceHullGhostFn_master_ok
    {keepR : BitVec 64 → Bool} {P_real : Program} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl)
    (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (durationSinceHullGhostFn keepR P_real mpl hullBase) masterDurationSinceSpec := by
  unfold durationSinceHullGhostFn
  rw [← hb1]
  refine durationSinceGhostFn_master_ok hpl hsvc_real
    (durationSinceHullProg_svc mpl) hreal_no (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
  rw [hb1, ← hb0]
  exact durationSinceHullProg_hasWords_durationSince mpl

/-- Concrete `80`-word contiguous hull Route-β′ master `HookOk` for `durationSinceHullGhostFnLs`. -/
theorem durationSinceHullGhostFnLs_masterLs_ok [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real : Program} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl)
    (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + subTimespecByteLen)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none) :
    HookOk (durationSinceHullGhostFnLs keepR P_real mpl hullBase)
      (withLsRet masterDurationSinceSpec) := by
  unfold durationSinceHullGhostFnLs
  rw [← hb1]
  refine durationSinceGhostFnLs_masterLs_ok hpl hsvc_real
    (durationSinceHullProg_svc mpl) hreal_no (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
  rw [hb1, ← hb0]
  exact durationSinceHullProg_hasWords_durationSince mpl

/-- Any non-`.Exception` evaluation of `durationSinceGhostFnLs` witnesses
    `LsRetAddr624 (u.readReg64 .lr)` (regardless of whether `roTableGuard` held). -/
theorem durationSinceGhostFnLs_lsRetAddr624_of_noException [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {u : State}
    (hnoex : ∀ msg,
      (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) :=
  lsRetAddr624_of_noException_via_activeRealPre
    linkedCallHookG_activeRealPre_of_noException hnoex

/-- K3-chained `noException ⇒ keepR (u.readReg64 .lr) = false` extractor for
    `durationSinceGhostFnLs` given `hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false`. -/
theorem durationSinceGhostFnLs_keepLr_false_of_noException [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {u : State}
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hnoex : ∀ msg,
      (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry u).status ≠ .Exception msg) :
    keepR (u.readReg64 .lr) = false :=
  keepLr_false_of_noException_via_activeRealPre
    hKeep linkedCallHookG_activeRealPre_of_noException hnoex

/-- Outside `LsRetAddr624 (s0.readReg64 .lr)`, `durationSinceGhostFnLs` returns `.Exception` across
    both `roTableGuard` branches. -/
theorem durationSinceGhostFnLs_of_not_lsRetAddr624 [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {s0 : State}
    (hnLr : ¬ LsRetAddr624 (s0.readReg64 .lr)) :
    durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  unfold durationSinceGhostFnLs
  by_cases hG : roTableGuard cst16Addr timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    exact linkedCallHook_withLsRet_of_not_lsRetAddr624 hnLr
  · rw [linkedCallHookG_eq_of_not_guard hG]
    have hnAct := not_activeRealPre_withLsRet_of_not_lsRetAddr624
      (master := masterDurationSinceSpec) hnLr
    simp only [hnAct, ↓reduceDIte]

open Classical in
/-- Behavior of `durationSinceGhostFn` when `keepR (s0.readReg64 .lr) = true`. -/
theorem durationSinceGhostFn_of_keepLr_true
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {s0 : State}
    (hlr : keepR (s0.readReg64 .lr) = true) :
    durationSinceGhostFn cst16Addr keepR P_real P_sub entry s0 =
      if _ : ActiveRealPre masterDurationSinceSpec s0 then
        durationSinceExactHook s0
      else
        { s0 with status := .Exception "ghost-hook precondition violated" } := by
  unfold durationSinceGhostFn
  rw [linkedCallHookG_of_keepLr_true hlr]
  by_cases hAct : ActiveRealPre masterDurationSinceSpec s0
  · simp only [hAct, ↓reduceDIte, keepFsTrace_durationSinceExactHook_eq]
  · simp only [hAct, ↓reduceDIte]

open Classical in
/-- Behavior of `durationSinceGhostFnLs` when `keepR (s0.readReg64 .lr) = true`. -/
theorem durationSinceGhostFnLs_of_keepLr_true [LibsignalPlacement]
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {s0 : State}
    (hlr : keepR (s0.readReg64 .lr) = true) :
    durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry s0 =
      if _ : ActiveRealPre (withLsRet masterDurationSinceSpec) s0 then
        durationSinceExactHook s0
      else
        { s0 with status := .Exception "ghost-hook precondition violated" } := by
  unfold durationSinceGhostFnLs
  rw [linkedCallHookG_of_keepLr_true hlr]
  by_cases hAct : ActiveRealPre (withLsRet masterDurationSinceSpec) s0
  · simp only [hAct, ↓reduceDIte, keepFsTrace_durationSinceExactHook_eq]
  · simp only [hAct, ↓reduceDIte]

/-! ## 3. C11 §8.1 State / VM / Trace Preservation Bundle (`fs`, `fsT`, `VmPreserved`, `OomPool`, `oracle`) -/

/-- C11 §8.1 obligation (1): `durationSinceGhostFn` preserves `State.fs` unconditionally. -/
theorem durationSinceGhostFn_fs
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry : BitVec 64) (s0 : State) :
    (durationSinceGhostFn cst16Addr keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHookG_fs (roTableGuard cst16Addr timePlacedData0)
    keepR P_real P_sub entry masterDurationSinceSpec durationSinceExactHook s0

/-- Route-β′ C11 §8.1 obligation (1): `durationSinceGhostFnLs` preserves `State.fs` unconditionally. -/
theorem durationSinceGhostFnLs_fs [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry : BitVec 64) (s0 : State) :
    (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry s0).fs = s0.fs :=
  linkedCallHookG_fs (roTableGuard cst16Addr timePlacedData0)
    keepR P_real P_sub entry (withLsRet masterDurationSinceSpec) durationSinceExactHook s0

/-- C11 §8.1 obligation (2): `durationSinceGhostFn` satisfies `HookFsTraced IsFsC` unconditionally. -/
theorem durationSinceGhostFn_fsT
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry : BitVec 64) :
    HookFsTraced IsFsC (durationSinceGhostFn cst16Addr keepR P_real P_sub entry) :=
  linkedCallHookG_fsT (roTableGuard cst16Addr timePlacedData0)
    keepR P_real P_sub entry masterDurationSinceSpec durationSinceExactHook

/-- Route-β′ C11 §8.1 obligation (2): `durationSinceGhostFnLs` satisfies `HookFsTraced IsFsC`
    unconditionally. -/
theorem durationSinceGhostFnLs_fsT [LibsignalPlacement]
    (cst16Addr : BitVec 64) (keepR : BitVec 64 → Bool) (P_real P_sub : Program)
    (entry : BitVec 64) :
    HookFsTraced IsFsC (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry) :=
  linkedCallHookG_fsT (roTableGuard cst16Addr timePlacedData0)
    keepR P_real P_sub entry (withLsRet masterDurationSinceSpec) durationSinceExactHook

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

private theorem subroutineStop_of_stdDurationSinceOutcome
    {tbl : BitVec 64} {x : DurationSinceGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withRoData tbl timePlacedData0 stdDurationSinceSpec) x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem activeRealRun_stdStatePreserved_and_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    {x : DurationSinceGhost} {R : SepProp} {s0 : State}
    (hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterDurationSinceSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keepR P_real P_sub (mpl.base 1) s0) :
    StdStatePreserved s0 (Classical.choose hReal.2.2.2) ∧
      (Classical.choose hReal.2.2.2).oracle = s0.oracle := by
  let s1 := s0.setPC (mpl.base 1)
  let s1' := stripS keepR s1
  have hG' : RoDataAt s1'.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0 :=
    roTableGuard_stripS keepR (mpl.base 1) (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
      hReal.1 hG
  have hs1_pre : s1.mem ⊨ stdDurationSinceSpec.pre x s1 ∗ R := by
    rw [stdDurationSince_pre_eq, masterDurationSince_pre_setPC]
    exact hpreM
  have hs1'_std : s1'.mem ⊨ stdDurationSinceSpec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keepR hs1_pre
    have heq : stdDurationSinceSpec.pre x s1' = stdDurationSinceSpec.pre x s1 := by
      dsimp only [s1']
      cases s1; rfl
    rwa [heq]
  have hs1'_pre :
      s1'.mem ⊨ (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        stdDurationSinceSpec).pre x s1' ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG', hs1'_std⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (subroutine_ok_stdDurationSince_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
      x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_stdDurationSinceOutcome hout'
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
  · dsimp only [withRoData, stdDurationSinceSpec] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : StdStatePreserved s1' sf' := hpost'.1
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
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem vmPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

private theorem durationSinceExactHook_oomPool_oracle (s : State) :
    (OomPreserved s (durationSinceExactHook s) ∧ PoolPreserved s (durationSinceExactHook s)) ∧
      (durationSinceExactHook s).oracle = s.oracle := by
  unfold durationSinceExactHook
  dsimp only
  split
  · exact ⟨⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, rfl⟩
  · split <;> (cases s; exact ⟨⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩, rfl⟩)

/-- Pointwise `VmPreserved` for `durationSinceGhostFn` across all guarded/unguarded branches. -/
theorem durationSinceGhostFn_vmPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    VmPreserved s0
      (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0) := by
  classical
  unfold durationSinceGhostFn
  by_cases hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
        exact vmPreserved_of_stdStatePreserved
          (activeRealRun_stdStatePreserved_and_oracle hpl hsvc_real hsvc_sub hreal_no hsub_no
            hw0 hw1 hG hrun hsp hpre hReal).1
      · rw [keepFsTrace_durationSinceExactHook_eq]
        exact durationSinceExactHook_vm s0
    · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [keepFsTrace_durationSinceExactHook_eq]
      exact durationSinceExactHook_vm s0
    · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `VmPreserved` for Route-β′ `durationSinceGhostFnLs` across all branches. -/
theorem durationSinceGhostFnLs_vmPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    VmPreserved s0
      (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0) := by
  classical
  unfold durationSinceGhostFnLs
  by_cases hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
        exact vmPreserved_of_stdStatePreserved
          (activeRealRun_stdStatePreserved_and_oracle hpl hsvc_real hsvc_sub hreal_no hsub_no
            hw0 hw1 hG hrun hsp (extract_withLsRet hpre).2 hReal).1
      · rw [keepFsTrace_durationSinceExactHook_eq]
        exact durationSinceExactHook_vm s0
    · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [keepFsTrace_durationSinceExactHook_eq]
      exact durationSinceExactHook_vm s0
    · exact LibsignalBinary.Heap.Fine.VmPreserved.of_eq rfl rfl rfl rfl rfl

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `durationSinceGhostFn`. -/
theorem durationSinceGhostFn_oomPoolPreserved
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    OomPreserved s0
        (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0) ∧
      PoolPreserved s0
        (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0) := by
  classical
  unfold durationSinceGhostFn
  by_cases hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
        exact oomPoolPreserved_of_stdStatePreserved
          (activeRealRun_stdStatePreserved_and_oracle hpl hsvc_real hsvc_sub hreal_no hsub_no
            hw0 hw1 hG hrun hsp hpre hReal).1
      · rw [keepFsTrace_durationSinceExactHook_eq]
        exact (durationSinceExactHook_oomPool_oracle s0).1
    · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [keepFsTrace_durationSinceExactHook_eq]
      exact (durationSinceExactHook_oomPool_oracle s0).1
    · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for Route-β′ `durationSinceGhostFnLs`. -/
theorem durationSinceGhostFnLs_oomPoolPreserved [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    OomPreserved s0
        (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0) ∧
      PoolPreserved s0
        (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0) := by
  classical
  unfold durationSinceGhostFnLs
  by_cases hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
        exact oomPoolPreserved_of_stdStatePreserved
          (activeRealRun_stdStatePreserved_and_oracle hpl hsvc_real hsvc_sub hreal_no hsub_no
            hw0 hw1 hG hrun hsp (extract_withLsRet hpre).2 hReal).1
      · rw [keepFsTrace_durationSinceExactHook_eq]
        exact (durationSinceExactHook_oomPool_oracle s0).1
    · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [keepFsTrace_durationSinceExactHook_eq]
      exact (durationSinceExactHook_oomPool_oracle s0).1
    · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `.oracle = s0.oracle` for `durationSinceGhostFn`. -/
theorem durationSinceGhostFn_oracle
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0).oracle =
      s0.oracle := by
  classical
  unfold durationSinceGhostFn
  by_cases hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
        exact (activeRealRun_stdStatePreserved_and_oracle hpl hsvc_real hsvc_sub hreal_no hsub_no
          hw0 hw1 hG hrun hsp hpre hReal).2
      · rw [keepFsTrace_durationSinceExactHook_eq]
        exact (durationSinceExactHook_oomPool_oracle s0).2
    · rfl
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [keepFsTrace_durationSinceExactHook_eq]
      exact (durationSinceExactHook_oomPool_oracle s0).2
    · rfl

/-- Pointwise `.oracle = s0.oracle` for Route-β′ `durationSinceGhostFnLs`. -/
theorem durationSinceGhostFnLs_oracle [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0).oracle =
      s0.oracle := by
  classical
  unfold durationSinceGhostFnLs
  by_cases hG : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    split
    · rename_i hActPre
      split
      · rename_i hReal
        rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
        exact (activeRealRun_stdStatePreserved_and_oracle hpl hsvc_real hsvc_sub hreal_no hsub_no
          hw0 hw1 hG hrun hsp (extract_withLsRet hpre).2 hReal).2
      · rw [keepFsTrace_durationSinceExactHook_eq]
        exact (durationSinceExactHook_oomPool_oracle s0).2
    · rfl
  · rw [linkedCallHookG_eq_of_not_guard hG]
    split
    · rw [keepFsTrace_durationSinceExactHook_eq]
      exact (durationSinceExactHook_oomPool_oracle s0).2
    · rfl

/-- Pointwise `.trace = s0.trace` for `durationSinceGhostFn`. -/
theorem durationSinceGhostFn_trace
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0).trace =
      s0.trace :=
  (durationSinceGhostFn_oomPoolPreserved
    hpl hsvc_real hsvc_sub hreal_no hsub_no hw0 hw1 s0).1.2.1

/-- Pointwise `.trace = s0.trace` for Route-β′ `durationSinceGhostFnLs`. -/
theorem durationSinceGhostFnLs_trace [LibsignalPlacement]
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    (s0 : State) :
    (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1) s0).trace =
      s0.trace :=
  (durationSinceGhostFnLs_oomPoolPreserved
    hpl hsvc_real hsvc_sub hreal_no hsub_no hw0 hw1 s0).1.2.1

/-! ## 4. Generic Route-β′ (`withLsRet`) Consumer Lift Combinators & Complete `HookOk` Suite -/

/-- Generic Route-β′ (`withLsRet`) lift from `masterDurationSinceSpec`:
    any `masterDurationSinceSpec ⇒ consumer` `HookOk` lift transfers automatically to
    `withLsRet masterDurationSinceSpec ⇒ withLsRet consumer` by routing states outside
    `LsRetAddr624` through `durationSinceExactHook` (`durationSinceExactHook_master_ok`) and
    evaluating at entry states `s0` satisfying `LsRetAddr624 (s0.readReg64 .lr)`. -/
theorem hookOk_withLsRet_of_master_lift [LibsignalPlacement] {β : Type}
    {f : State → State} {consumer : Spec β}
    (hlift : ∀ g : State → State, HookOk g masterDurationSinceSpec → HookOk g consumer)
    (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet consumer) := by
  classical
  let g : State → State :=
    fun s => if LsRetAddr624 (s.readReg64 .lr) then f s else durationSinceExactHook s
  have hg_master : HookOk g masterDurationSinceSpec := by
    intro x R s hrun hpre hsp
    by_cases hlr : LsRetAddr624 (s.readReg64 .lr)
    · have hge : g s = f s := by simp only [g, hlr, ↓reduceIte]
      rw [hge]
      exact hh x R s hrun (intro_withLsRet hlr hpre) hsp
    · have hge : g s = durationSinceExactHook s := by simp only [g, hlr, ↓reduceIte]
      rw [hge]
      exact durationSinceExactHook_master_ok x R s hrun hpre hsp
  have hg_cons : HookOk g consumer := hlift g hg_master
  intro y R s0 hrun hpre hsp
  obtain ⟨hlr0, hpre0⟩ := extract_withLsRet hpre
  have hg0 : g s0 = f s0 := by simp only [g, hlr0, ↓reduceIte]
  simpa only [withLsRet_outcome_eq, hg0] using hg_cons y R s0 hrun hpre0 hsp

/-- `VmPreserved`-aware Route-β′ (`withLsRet`) lift from `masterDurationSinceSpec`:
    transfers any `(HookOk g masterDurationSinceSpec → (∀ s, VmPreserved s (g s)) → HookOk g consumer)`
    lift to `withLsRet` using `durationSinceExactHook_vm` outside `LsRetAddr624`. -/
theorem hookOk_withLsRet_of_master_vm_lift [LibsignalPlacement] {β : Type}
    {f : State → State} {consumer : Spec β}
    (hlift : ∀ g : State → State,
      HookOk g masterDurationSinceSpec → (∀ s, VmPreserved s (g s)) → HookOk g consumer)
    (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet consumer) := by
  classical
  let g : State → State :=
    fun s => if LsRetAddr624 (s.readReg64 .lr) then f s else durationSinceExactHook s
  have hg_master : HookOk g masterDurationSinceSpec := by
    intro x R s hrun hpre hsp
    by_cases hlr : LsRetAddr624 (s.readReg64 .lr)
    · have hge : g s = f s := by simp only [g, hlr, ↓reduceIte]
      rw [hge]
      exact hh x R s hrun (intro_withLsRet hlr hpre) hsp
    · have hge : g s = durationSinceExactHook s := by simp only [g, hlr, ↓reduceIte]
      rw [hge]
      exact durationSinceExactHook_master_ok x R s hrun hpre hsp
  have hg_vm : ∀ s, VmPreserved s (g s) := by
    intro s
    by_cases hlr : LsRetAddr624 (s.readReg64 .lr)
    · have hge : g s = f s := by simp only [g, hlr, ↓reduceIte]
      rw [hge]; exact hvm s
    · have hge : g s = durationSinceExactHook s := by simp only [g, hlr, ↓reduceIte]
      rw [hge]; exact durationSinceExactHook_vm s
  have hg_cons : HookOk g consumer := hlift g hg_master hg_vm
  intro y R s0 hrun hpre hsp
  obtain ⟨hlr0, hpre0⟩ := extract_withLsRet hpre
  have hg0 : g s0 = f s0 := by simp only [g, hlr0, ↓reduceIte]
  simpa only [withLsRet_outcome_eq, hg0] using hg_cons y R s0 hrun hpre0 hsp

/-! ### 4a. Route-β′ `withLsRet` Consumer Lifts (Generic in `f : State → State`) -/

theorem hookOk_withLsRet_durationSinceBoundedAt_keepsFs_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (durationSinceBoundedAtSpec stk).keepsFs) :=
  hookOk_withLsRet_of_master_lift
    (fun _ hg => hookOk_durationSinceBoundedAt_keepsFs_of_master hg hstk) hh

theorem hookOk_withLsRet_durationSinceBoundedAt_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (durationSinceBoundedAtSpec stk)) :=
  hookOk_withLsRet_of_master_lift
    (fun _ hg => hookOk_durationSinceBoundedAt_of_master hg hstk) hh

theorem hookOk_withLsRet_durationSinceBounded_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet durationSinceBoundedSpec) :=
  hookOk_withLsRet_of_master_lift (fun _ hg => hookOk_durationSinceBounded_of_master hg) hh

theorem hookOk_withLsRet_durationSinceBounded_keepsFs_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet durationSinceBoundedSpec.keepsFs) :=
  hookOk_withLsRet_of_master_lift (fun _ hg => hookOk_durationSinceBounded_keepsFs_of_master hg) hh

theorem hookOk_withLsRet_durationSinceBoundedAlloc_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet durationSinceBoundedAllocSpec) :=
  hookOk_withLsRet_of_master_lift (fun _ hg => hookOk_durationSinceBoundedAlloc_of_master hg) hh

theorem hookOk_withLsRet_durationSinceBoundedBudgetAt_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (durationSinceBoundedBudgetAtSpec stk)) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceBoundedBudgetAt_of_master hg hgv hstk) hh hvm

theorem hookOk_withLsRet_durationSinceBoundedBudget_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet durationSinceBoundedBudgetSpec) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceBoundedBudget_of_master hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceBoundedBudget_keepsFs_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet durationSinceBoundedBudgetSpec.keepsFs) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceBoundedBudget_keepsFs_of_master hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceBoundedAllocBudget_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet durationSinceBoundedAllocBudgetSpec) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceBoundedAllocBudget_of_master hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceBounded_inImage_of_master [LibsignalPlacement]
    {f : State → State} (img : Image) (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet (durationSinceBoundedSpec.inImage img)) :=
  hookOk_withLsRet_of_master_lift
    (fun _ hg => hookOk_durationSinceBounded_inImage_of_master img hg) hh

theorem hookOk_withLsRet_durationSinceBoundedBudget_inImage_of_master [LibsignalPlacement]
    {f : State → State} (img : Image) (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet (durationSinceBoundedBudgetSpec.inImage img)) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceBoundedBudget_inImage_of_master img hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceEpochAt_keepsFs_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (durationSinceEpochAtSpec stk).keepsFs) :=
  hookOk_withLsRet_of_master_lift
    (fun _ hg => hookOk_durationSinceEpochAt_keepsFs_of_master hg hstk) hh

theorem hookOk_withLsRet_durationSinceEpochAt_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (durationSinceEpochAtSpec stk)) :=
  hookOk_withLsRet_of_master_lift
    (fun _ hg => hookOk_durationSinceEpochAt_of_master hg hstk) hh

theorem hookOk_withLsRet_durationSinceEpoch_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet durationSinceEpochSpec) :=
  hookOk_withLsRet_of_master_lift (fun _ hg => hookOk_durationSinceEpoch_of_master hg) hh

theorem hookOk_withLsRet_durationSinceEpoch_keepsFs_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet durationSinceEpochSpec.keepsFs) :=
  hookOk_withLsRet_of_master_lift (fun _ hg => hookOk_durationSinceEpoch_keepsFs_of_master hg) hh

theorem hookOk_withLsRet_durationSinceEpochAlloc_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet durationSinceEpochAllocSpec) :=
  hookOk_withLsRet_of_master_lift (fun _ hg => hookOk_durationSinceEpochAlloc_of_master hg) hh

theorem hookOk_withLsRet_durationSinceEpochBudgetAt_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withLsRet (withVmPreserved (durationSinceEpochAtSpec stk))) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceEpochBudgetAt_of_master hg hgv hstk) hh hvm

theorem hookOk_withLsRet_durationSinceEpochBudget_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet durationSinceEpochBudgetSpec) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceEpochBudget_of_master hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceEpochBudget_keepsFs_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet durationSinceEpochBudgetSpec.keepsFs) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceEpochBudget_keepsFs_of_master hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceEpochAllocBudget_of_master [LibsignalPlacement]
    {f : State → State} (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet durationSinceEpochAllocBudgetSpec) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceEpochAllocBudget_of_master hg hgv) hh hvm

theorem hookOk_withLsRet_durationSinceEpoch_inImage_of_master [LibsignalPlacement]
    {f : State → State} (img : Image) (hh : HookOk f (withLsRet masterDurationSinceSpec)) :
    HookOk f (withLsRet (durationSinceEpochSpec.inImage img)) :=
  hookOk_withLsRet_of_master_lift
    (fun _ hg => hookOk_durationSinceEpoch_inImage_of_master img hg) hh

theorem hookOk_withLsRet_durationSinceEpochBudget_inImage_of_master [LibsignalPlacement]
    {f : State → State} (img : Image) (hh : HookOk f (withLsRet masterDurationSinceSpec))
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withLsRet (durationSinceEpochBudgetSpec.inImage img)) :=
  hookOk_withLsRet_of_master_vm_lift
    (fun _ hg hgv => hookOk_durationSinceEpochBudget_inImage_of_master img hg hgv) hh hvm

/-! ### 4b. Generic Wrapper Combinators (`keepsFs`, `withOomPoolPreserved`, `withExecFrozen`) -/

theorem durationSinceGhostFn_any_keepsFs_ok {α : Type}
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (durationSinceGhostFn cst16Addr keepR P_real P_sub entry) spec) :
    HookOk (durationSinceGhostFn cst16Addr keepR P_real P_sub entry) spec.keepsFs :=
  hh.keepsFs (durationSinceGhostFn_fs cst16Addr keepR P_real P_sub entry)

theorem durationSinceGhostFnLs_any_keepsFs_ok [LibsignalPlacement] {α : Type}
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry) (withLsRet spec)) :
    HookOk (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry)
      (withLsRet spec.keepsFs) := by
  rw [withLsRet_keepsFs]
  exact hh.keepsFs (durationSinceGhostFnLs_fs cst16Addr keepR P_real P_sub entry)

theorem durationSinceGhostFn_any_withOomPoolPreserved_ok {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    {spec : Spec α}
    (hh : HookOk (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1))
      spec) :
    HookOk (durationSinceGhostFn (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1))
      (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (durationSinceGhostFn_oomPoolPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hw0 hw1)

theorem durationSinceGhostFnLs_any_withOomPoolPreserved_ok [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl))
    {spec : Spec α}
    (hh : HookOk (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1))
      (withLsRet spec)) :
    HookOk (durationSinceGhostFnLs (mpl.ρ timeRodataCst16Sym) keepR P_real P_sub (mpl.base 1))
      (withLsRet (withOomPoolPreserved spec)) := by
  rw [withLsRet_withOomPoolPreserved]
  exact hookOk_withOomPoolPreserved hh
    (durationSinceGhostFnLs_oomPoolPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hw0 hw1)

theorem durationSinceGhostFn_any_execFrozen_ok {α : Type}
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (durationSinceGhostFn cst16Addr keepR P_real P_sub entry) spec) :
    HookOk (durationSinceGhostFn cst16Addr keepR P_real P_sub entry)
      (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

theorem durationSinceGhostFnLs_any_execFrozen_ok [LibsignalPlacement] {α : Type}
    {cst16Addr : BitVec 64} {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entry : BitVec 64} {spec : Spec α}
    (hh : HookOk (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry) (withLsRet spec)) :
    HookOk (durationSinceGhostFnLs cst16Addr keepR P_real P_sub entry)
      (withLsRet (withExecFrozen spec)) := by
  rw [withLsRet_withExecFrozen]
  exact hookOk_withExecFrozen_of_plain hh

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost
