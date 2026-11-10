/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode

/-!
# `W`-Independent Ghost `from_utf8` Hook, Consumer `HookOk` Suite, & Stock-Safe `_liftVis` Replays (`HooksDehook.FromUtf8Ghost`)

Card **R1-b** for de-hooking `core::str::converts::from_utf8` (`lsFromUtf8Sym`, `156` words =
`624` bytes from `VerifiedLibraries.RustStd.coreMultiLib.blockLib 1` — rustup musl sysroot `core`
rlib `Cs2kXltWtc1W`; the CLI's own `core` is `CskxtBwYRO61I`, matching `624` B, with placed-block
byte identity deferred to Card R1-a2 after STOCK commit 1 via reloc-masked compare +
`fetch_rebase_of_patchedWord` / `patchedWord_block_some`):

1. **`W`-Independent Guarded Ghost Hook (`fromUtf8GhostHook`, `emptyFromUtf8GhostHook`):**
   Wraps `masterFromUtf8Spec` (and `fromUtf8SpecK keep masterFromUtf8Spec`) via
   `linkedCallHookG (roTableGuard tbl corePlacedData1)` with the computable `W`-free fallback
   `realFromUtf8Fallback`. Specializing `P_run := emptyStdProg` (`= hole2_emptyProg`) and
   `P_sub := pureWordsProg pl.base (fromUtf8PatchedWords pl)` yields `emptyFromUtf8GhostHook keep pl`
   and `emptyFromUtf8GhostHookK keep pl` with **zero dependence on `W : CliHooks`**.

2. **Pointwise State Preservation (`fs`, `HookFsTraced IsFsC`, `VmPreserved`, `OomPreserved`):**
   - `fromUtf8GhostHook_fs` / `fromUtf8GhostHook_fsT` hold unconditionally via `linkedCallHookG_fs`
     and `linkedCallHookG_fsT`.
   - `fromUtf8GhostHook_vmPreserved` / `fromUtf8GhostHook_oomPoolPreserved` extract full
     `ProcessFieldsPreserved` on the active real-code branch via `processFromUtf8Spec` +
     `roTableGuard_stripS` + `perm_eq_of_stripExecOutside_keepsFrozen`, and delegate to
     `realFromUtf8Fallback_vmPreserved` on the fallback branch.

3. **Complete Consumer `HookOk` Suite (All `stk : Nat`, RW & RO):**
   Discharges `HookOk` for `masterFromUtf8Spec`, `MainHops.fromUtf8AsciiSpec stk` (`=
   FromUtf8.fromUtf8AsciiSpec stk`), `CalleesRO.fromUtf8AsciiSpecRO stk`, `CliExt.fromUtf8Spec`,
   and their `.keepsFs`, `withVmPreserved` (matching `ElfSlicesPqOomH2KHooks.lean:365` and
   `CliHookSatPlacedBudget.lean:296`), `withOomPoolPreserved`, `.inImage`, and `fromUtf8SpecK`
   variants.

4. **Stock-Safe `StepsVisitedIn` & `_roTable_liftVis` Replays (`REV-S1` F1):**
   Uses `linkedCallHookG_visitedIn` and `ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis`
   (taking `hLiftVis : … → h2fsgen_StepsVisitedIn keep P_run (u.setPC pl.base) sf →
   Steps P_real (u.setPC pl.base) sf`, discharged on stock ELF via
   `h2sl_steps_realW_of_visitedIn_keepSub`, never `h2sl_stepsUntil_emptyProg_to_realW`).

### C11 Bundle Mapping Note (No `GhostRowSpecOk` Redefined Here)
When C11 Commit 2B wires the `lsFromUtf8Sym` row into `CliGhostHooks.extra`:
- **`f` (`State → State`, `W`-independent):** `emptyFromUtf8GhostHook keep pl` (or `…K keep pl`).
- **`fs_eq`:** `emptyFromUtf8GhostHook_fs keep pl` (`∀ s, (f s).fs = s.fs`).
- **`fsT` (`HookFsTraced IsFsC f`):** `emptyFromUtf8GhostHook_fsT keep pl`.
- **`vmPreserved` (`∀ s, VmPreserved s (f s)`):** `emptyFromUtf8GhostHook_vmPreserved keep hpl`.
- **Consumer `HookOk` (`GhostRowSpecOk`):**
  - RW budget/K consumers (`∀ stk, HookOk f (withVmPreserved (fromUtf8AsciiSpec stk))`):
    `emptyFromUtf8GhostHook_ascii_vmPreserved_ok keep hpl stk`
    (and `emptyFromUtf8GhostHookK_asciiK_vmPreserved_ok keep hpl stk`).
  - RO budget consumers (`∀ stk, HookOk f (withVmPreserved (fromUtf8AsciiSpecRO stk))`):
    `emptyFromUtf8GhostHook_asciiRO_vmPreserved_ok keep hpl stk`.
- **Stock-ELF `On`/`S` Replay (`GhostRowReplayOn`, C11 §8.2):**
  `ghostExternReplaysOn_emptyFromUtf8GhostHook_liftVis` (or `…K_autoLr_liftVis`) instantiated with
  `InvMem := F3CodeInv mpl mmpl` (preserved across real hooks via `linkedCallHookG_fs`), `hRoInv`
  from C2 §3 `f3CodeInv_roDataAt_*` for `corePlacedData1`, and `hLiftVis` from
  `h2sl_steps_realW_of_visitedIn_keepSub`.
- **C1 Activation Follow-Up (before flip 2):** Switch `#1328`'s raw
  `cliGhostExterns_fromUtf8_eq` call sites (`ElfSlicesPqOomH2KD3MainLiftGlueSat.lean`,
  `ElfSlicesPqOomH2KMainEntryFitsSat.lean`) to `hookSat_withExtra_of_base … hG.extraOk`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost

open Arm64 ProofLib SepProp
open Arm64.Obj (Placement)
open Arm64.Process (pureWordsProg)
open VerifiedLibraries.RustStd (coreUtf8CharWidthSym corePlacedData1)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (fromUtf8Spec)
open CryptoVerification.SignalSession.Cli.MainHops (fromUtf8AsciiSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen ActiveRealPre ActiveRealRun keepFsTrace
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_single_stub ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  roTableGuard linkedCallHookG
  linkedCallHookG_eq_conj linkedCallHookG_activeRealPre_of_noException
  linkedCallHookG_of_keepLr_true linkedCallHookG_fs linkedCallHookG_fsT
  linkedCallHookG_visitedIn roTableGuard_stripS
  hookOk_linkedCallHookG_roTable
  ghostExternReplaysOn_of_linkedCallHookG_roTable
  ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  memsetSpecK pureWordsProg_externAt_none hookOk_memsetSpecK_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_svc emptyStdProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  vmPreserved_of_processFieldsPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (
  fromUtf8Block fromUtf8PatchedWords pureWordsProg_fromUtf8_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code (
  FromUtf8Call masterFromUtf8Spec processFromUtf8Spec fromUtf8SpecK
  processFromUtf8Spec_pre_eq
  subroutine_ok_processFromUtf8_of_hasWords
  subroutine_ok_masterFromUtf8_of_hasWords
  subroutine_ok_masterFromUtf8K_of_hasWords
  realFromUtf8Fallback
  realFromUtf8Fallback_processFieldsPreserved
  keepFsTrace_realFromUtf8Fallback_eq_apply
  keepFsTrace_realFromUtf8Fallback_master_ok
  keepFsTrace_realFromUtf8Fallback_masterK_ok
  hookOk_of_specSimulates specSimulates_inImage
  specStripSInvariant_masterFromUtf8 specStripSInvariant_masterFromUtf8K
  specPreservesFsTrace_masterFromUtf8 specPreservesFsTrace_masterFromUtf8K
  masterFromUtf8_pre_setPC processFromUtf8_pre_setPC masterFromUtf8K_pre_setPC
  masterFromUtf8_outcome_setPC masterFromUtf8K_outcome_setPC
  hookOk_fromUtf8Ascii_of_master hookOk_fromUtf8Ascii_keepsFs_of_master
  hookOk_cliFromUtf8_of_master hookOk_cliFromUtf8_keepsFs_of_master
  hookOk_fromUtf8AsciiRO_of_master hookOk_fromUtf8AsciiRO_keepsFs_of_master
  hookOk_fromUtf8AsciiK_of_master hookOk_fromUtf8AsciiK_keepsFs_of_master
  hookOk_cliFromUtf8K_of_master
  hookOk_fromUtf8AsciiROK_of_master hookOk_fromUtf8AsciiROK_keepsFs_of_master
  fromUtf8SpecK_keepsFs fromUtf8SpecK_withVmPreserved fromUtf8SpecK_withOomPoolPreserved
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det
)

/-! ## 1. `W`-Independent Ghost `from_utf8` Hook Definitions & `keep` Coverage -/

/-- Guarded ghost `from_utf8` hook wrapping `masterFromUtf8Spec` under
    `roTableGuard tbl corePlacedData1` with the `W`-independent fallback `realFromUtf8Fallback`. -/
@[expose] noncomputable def fromUtf8GhostHook
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHookG (roTableGuard tbl corePlacedData1) keep P_real P_sub entryTarget
    masterFromUtf8Spec realFromUtf8Fallback

/-- `K`-narrowed guarded ghost `from_utf8` hook wrapping `fromUtf8SpecK keep masterFromUtf8Spec`
    under `roTableGuard tbl corePlacedData1` with `realFromUtf8Fallback`. -/
@[expose] noncomputable def fromUtf8GhostHookK
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHookG (roTableGuard tbl corePlacedData1) keep P_real P_sub entryTarget
    (fromUtf8SpecK keep masterFromUtf8Spec) realFromUtf8Fallback

/-- Specialization of `fromUtf8GhostHook` to the single-block `pureWordsProg` hull of `pl`. -/
noncomputable abbrev fromUtf8GhostHookPure
    (keep : BitVec 64 → Bool) (P_real : Program) (pl : Placement) : State → State :=
  fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real
    (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base

/-- Specialization of `fromUtf8GhostHookK` to the single-block `pureWordsProg` hull of `pl`. -/
noncomputable abbrev fromUtf8GhostHookPureK
    (keep : BitVec 64 → Bool) (P_real : Program) (pl : Placement) : State → State :=
  fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real
    (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base

/-- Fully `W`-independent ghost `from_utf8` hook specialized to `P_run = emptyStdProg`
    (`= hole2_emptyProg`) and `P_sub = pureWordsProg pl.base (fromUtf8PatchedWords pl)`. -/
noncomputable abbrev emptyFromUtf8GhostHook
    (keep : BitVec 64 → Bool) (pl : Placement) : State → State :=
  fromUtf8GhostHookPure keep emptyStdProg pl

/-- Fully `W`-independent `K`-narrowed ghost `from_utf8` hook specialized to `P_run = emptyStdProg`
    and `P_sub = pureWordsProg pl.base (fromUtf8PatchedWords pl)`. -/
noncomputable abbrev emptyFromUtf8GhostHookK
    (keep : BitVec 64 → Bool) (pl : Placement) : State → State :=
  fromUtf8GhostHookPureK keep emptyStdProg pl

/-- Minimal placement-generic `keep` predicate retaining only the `624`-byte `from_utf8` block. -/
@[expose] def keepFromUtf8Block (entryTarget : BitVec 64) (a : BitVec 64) : Bool :=
  decide ((a - entryTarget).toNat < 624)

/-- Coverage condition stating that `keep` retains all `624` bytes (`156` words) of `from_utf8`. -/
@[expose] def KeepCoversFromUtf8 (keep : BitVec 64 → Bool) (entryTarget : BitVec 64) : Prop :=
  ∀ off : Nat, off < 624 → keep (entryTarget + BitVec.ofNat 64 off) = true

theorem keepCoversFromUtf8_keepFromUtf8Block (entryTarget : BitVec 64) :
    KeepCoversFromUtf8 (keepFromUtf8Block entryTarget) entryTarget := by
  intro off hoff
  unfold keepFromUtf8Block
  have hsub : entryTarget + BitVec.ofNat 64 off - entryTarget = BitVec.ofNat 64 off := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hoff

theorem keepCoversFromUtf8_of_range
    {keep : BitVec 64 → Bool} {entryTarget : BitVec 64} (lo hi : Nat)
    (hrange : ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → keep a = true)
    (hlo : lo ≤ entryTarget.toNat)
    (hhi : entryTarget.toNat + 624 ≤ hi)
    (hnowrap : entryTarget.toNat + 624 ≤ 2 ^ 64) :
    KeepCoversFromUtf8 keep entryTarget := by
  intro off hoff
  have hadd : (entryTarget + BitVec.ofNat 64 off).toNat = entryTarget.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : entryTarget.toNat + off < 2 ^ 64)]
  exact hrange _ (by omega) (by omega)

/-! ## 2. Pointwise State Preservation (`fs`, `HookFsTraced IsFsC`, `VmPreserved`, `OomPreserved`) -/

theorem fromUtf8GhostHook_fs
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (s0 : State) :
    (fromUtf8GhostHook tbl keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHookG_fs (roTableGuard tbl corePlacedData1) keep P_real P_sub entryTarget
    masterFromUtf8Spec realFromUtf8Fallback s0

theorem fromUtf8GhostHookK_fs
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (s0 : State) :
    (fromUtf8GhostHookK tbl keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHookG_fs (roTableGuard tbl corePlacedData1) keep P_real P_sub entryTarget
    (fromUtf8SpecK keep masterFromUtf8Spec) realFromUtf8Fallback s0

theorem fromUtf8GhostHook_fsT
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (fromUtf8GhostHook tbl keep P_real P_sub entryTarget) :=
  linkedCallHookG_fsT (roTableGuard tbl corePlacedData1) keep P_real P_sub entryTarget
    masterFromUtf8Spec realFromUtf8Fallback

theorem fromUtf8GhostHookK_fsT
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (fromUtf8GhostHookK tbl keep P_real P_sub entryTarget) :=
  linkedCallHookG_fsT (roTableGuard tbl corePlacedData1) keep P_real P_sub entryTarget
    (fromUtf8SpecK keep masterFromUtf8Spec) realFromUtf8Fallback

theorem emptyFromUtf8GhostHook_fs
    (keep : BitVec 64 → Bool) (pl : Placement) (s0 : State) :
    (emptyFromUtf8GhostHook keep pl s0).fs = s0.fs :=
  fromUtf8GhostHook_fs _ keep _ _ _ s0

theorem emptyFromUtf8GhostHookK_fs
    (keep : BitVec 64 → Bool) (pl : Placement) (s0 : State) :
    (emptyFromUtf8GhostHookK keep pl s0).fs = s0.fs :=
  fromUtf8GhostHookK_fs _ keep _ _ _ s0

theorem emptyFromUtf8GhostHook_fsT
    (keep : BitVec 64 → Bool) (pl : Placement) :
    HookFsTraced IsFsC (emptyFromUtf8GhostHook keep pl) :=
  fromUtf8GhostHook_fsT _ keep _ _ _

theorem emptyFromUtf8GhostHookK_fsT
    (keep : BitVec 64 → Bool) (pl : Placement) :
    HookFsTraced IsFsC (emptyFromUtf8GhostHookK keep pl) :=
  fromUtf8GhostHookK_fsT _ keep _ _ _

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

private theorem subroutineStop_of_processFromUtf8Outcome
    {tbl : BitVec 64} {x : FromUtf8Call} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome (withRoData tbl corePlacedData1 processFromUtf8Spec) x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩
    rw [hret.2.2]; decide
  · dsimp only [withRoData, processFromUtf8Spec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [withRoData, processFromUtf8Spec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withRoData, processFromUtf8Spec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- Shared real-run `ProcessFieldsPreserved` extractor on the active guarded branch when `s0`
    satisfies `roTableGuard (pl.ρ corePlacedData1)` and `masterFromUtf8Spec.pre`. -/
private theorem activeRealRun_processFieldsPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    {x : FromUtf8Call} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterFromUtf8Spec.pre x s0 ∗ R)
    (hG : roTableGuard (pl.ρ coreUtf8CharWidthSym) corePlacedData1 s0)
    (hReal : ActiveRealRun keep P_real P_sub pl.base s0) :
    ProcessFieldsPreserved s0 (Classical.choose hReal.2.2.2) := by
  let tbl := pl.ρ coreUtf8CharWidthSym
  let s1 := s0.setPC pl.base
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ processFromUtf8Spec.pre x s1 ∗ R := by
    rw [processFromUtf8_pre_setPC x s0 pl.base, processFromUtf8Spec_pre_eq]
    exact hpreM
  have hs1'_pre_inner : s1'.mem ⊨ processFromUtf8Spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : processFromUtf8Spec.pre x s1' = processFromUtf8Spec.pre x s1 := by
      rw [processFromUtf8Spec_pre_eq]
      exact (specStripSInvariant_masterFromUtf8 keep).pre_eq x s1
    rwa [heq]
  have hG' : RoDataAt s1'.mem tbl corePlacedData1 :=
    roTableGuard_stripS keep pl.base tbl corePlacedData1 s0 hReal.1 hG
  have hs1'_pre :
      s1'.mem ⊨ (withRoData tbl corePlacedData1 processFromUtf8Spec).pre x s1' ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG', hs1'_pre_inner⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (subroutine_ok_processFromUtf8_of_hasWords hpl hsub_no hwords)
      x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_processFromUtf8Outcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withRoData, processFromUtf8Spec] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : ProcessFieldsPreserved s1' sf' := hpost'.1
    rw [hsf_eq] at hstd'
    have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf
        huntil.toSteps.keepsFrozen hstd'.2.2.2.2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩
    · cases s0; cases sf; exact hstd'.1
    · cases s0; cases sf; exact hstd'.2.1
    · cases s0; cases sf; exact hstd'.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.2.1
    · cases s0; cases sf; exact hstd'.2.2.2.2.2.2.1
  · dsimp only [withRoData, processFromUtf8Spec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [withRoData, processFromUtf8Spec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [withRoData, processFromUtf8Spec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem oomPoolPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

private theorem pureWordsProg_svc (base : BitVec 64) (words : List (BitVec 32)) :
    (pureWordsProg base words).svc = Syscall.standard := by
  unfold pureWordsProg Program.ofWords
  rfl

/-- Pointwise `ProcessFieldsPreserved` for `fromUtf8GhostHook` across all three branches
    (`ActiveRealRun` under `roTableGuard`, `realFromUtf8Fallback`, and `.Exception`). -/
theorem fromUtf8GhostHook_processFieldsPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    ProcessFieldsPreserved s0
      (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) := by
  classical
  unfold fromUtf8GhostHook; rw [linkedCallHookG_eq_conj]; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact activeRealRun_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre hReal.1 hReal.2
    · rw [keepFsTrace_realFromUtf8Fallback_eq_apply]
      exact realFromUtf8Fallback_processFieldsPreserved s0
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Pointwise `ProcessFieldsPreserved` for `fromUtf8GhostHookK` across all three branches. -/
theorem fromUtf8GhostHookK_processFieldsPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    ProcessFieldsPreserved s0
      (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) := by
  classical
  unfold fromUtf8GhostHookK; rw [linkedCallHookG_eq_conj]; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [fromUtf8SpecK, memsetSpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact activeRealRun_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords
        hrun hsp hpre.2 hReal.1 hReal.2
    · rw [keepFsTrace_realFromUtf8Fallback_eq_apply]
      exact realFromUtf8Fallback_processFieldsPreserved s0
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem fromUtf8GhostHook_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    VmPreserved s0 (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) :=
  vmPreserved_of_processFieldsPreserved
    (fromUtf8GhostHook_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords s0)

theorem fromUtf8GhostHookK_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    VmPreserved s0 (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) :=
  vmPreserved_of_processFieldsPreserved
    (fromUtf8GhostHookK_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords s0)

theorem fromUtf8GhostHook_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    OomPreserved s0 (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) ∧
      PoolPreserved s0 (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) :=
  oomPoolPreserved_of_processFieldsPreserved
    (fromUtf8GhostHook_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords s0)

theorem fromUtf8GhostHookK_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    OomPreserved s0 (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) ∧
      PoolPreserved s0 (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0) :=
  oomPoolPreserved_of_processFieldsPreserved
    (fromUtf8GhostHookK_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords s0)

theorem fromUtf8GhostHook_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0).trace = s0.trace :=
  (fromUtf8GhostHook_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords s0).2.1

theorem fromUtf8GhostHookK_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) (s0 : State) :
    (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base s0).trace = s0.trace :=
  (fromUtf8GhostHookK_processFieldsPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords s0).2.1

/-- Along any non-`.Exception` call step of `fromUtf8GhostHookK`, `keep (u.readReg64 .lr) = false`
    holds automatically (the `K`-route `lr ∉ keep` extractor). -/
theorem fromUtf8GhostHookK_keepLr_false_of_noException
    {tbl : BitVec 64} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg,
      (fromUtf8GhostHookK tbl keep P_real P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  have hActPre : ActiveRealPre (fromUtf8SpecK keep masterFromUtf8Spec) u :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  rcases hActPre with ⟨_, _, x, R, hpre⟩
  dsimp only [fromUtf8SpecK, memsetSpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of plain `fromUtf8GhostHook` when `keep (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterFromUtf8Spec s0` holds: evaluates to `realFromUtf8Fallback s0`. -/
theorem fromUtf8GhostHook_of_keepLr_true
    {tbl : BitVec 64} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterFromUtf8Spec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    fromUtf8GhostHook tbl keep P_real P_sub entryTarget s0 = realFromUtf8Fallback s0 := by
  classical
  unfold fromUtf8GhostHook
  rw [linkedCallHookG_of_keepLr_true hlr_in]
  simp only [hActPre, ↓reduceDIte]
  exact keepFsTrace_realFromUtf8Fallback_eq_apply s0

/-- Behavior of `K`-narrowed `fromUtf8GhostHookK` when `keep (s0.readReg64 .lr) = true`:
    evaluates to `{ s0 with status := .Exception "ghost-hook precondition violated" }`. -/
theorem fromUtf8GhostHookK_of_keepLr_true
    {tbl : BitVec 64} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State}
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    fromUtf8GhostHookK tbl keep P_real P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (fromUtf8SpecK keep masterFromUtf8Spec) s0 := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [fromUtf8SpecK, memsetSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keep (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold fromUtf8GhostHookK
  rw [linkedCallHookG_of_keepLr_true hlr_in]
  simp only [hnAct, ↓reduceDIte]

theorem emptyFromUtf8GhostHook_vmPreserved
    (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl) (s0 : State) :
    VmPreserved s0 (emptyFromUtf8GhostHook keep pl s0) :=
  fromUtf8GhostHook_vmPreserved hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) s0

theorem emptyFromUtf8GhostHookK_vmPreserved
    (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl) (s0 : State) :
    VmPreserved s0 (emptyFromUtf8GhostHookK keep pl s0) :=
  fromUtf8GhostHookK_vmPreserved hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) s0

theorem emptyFromUtf8GhostHook_oomPoolPreserved
    (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl) (s0 : State) :
    OomPreserved s0 (emptyFromUtf8GhostHook keep pl s0) ∧
      PoolPreserved s0 (emptyFromUtf8GhostHook keep pl s0) :=
  fromUtf8GhostHook_oomPoolPreserved hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) s0

theorem emptyFromUtf8GhostHookK_oomPoolPreserved
    (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl) (s0 : State) :
    OomPreserved s0 (emptyFromUtf8GhostHookK keep pl s0) ∧
      PoolPreserved s0 (emptyFromUtf8GhostHookK keep pl s0) :=
  fromUtf8GhostHookK_oomPoolPreserved hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) s0

theorem emptyFromUtf8GhostHook_trace
    (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl) (s0 : State) :
    (emptyFromUtf8GhostHook keep pl s0).trace = s0.trace :=
  fromUtf8GhostHook_trace hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) s0

theorem emptyFromUtf8GhostHookK_trace
    (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl) (s0 : State) :
    (emptyFromUtf8GhostHookK keep pl s0).trace = s0.trace :=
  fromUtf8GhostHookK_trace hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) s0

theorem emptyFromUtf8GhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {pl : Placement} {u : State}
    (hnoex : ∀ msg, (emptyFromUtf8GhostHookK keep pl u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false :=
  fromUtf8GhostHookK_keepLr_false_of_noException hnoex

/-! ## 3. Master & Consumer `HookOk` Suite (All `stk : Nat`, RW & RO, Plain & `K`) -/

/-- Master `HookOk` of `fromUtf8GhostHook` for `masterFromUtf8Spec` on any hook-free `P_sub`
    holding `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem fromUtf8GhostHook_master_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      masterFromUtf8Spec :=
  hookOk_linkedCallHookG_roTable hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterFromUtf8_of_hasWords hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8 keep)
    specPreservesFsTrace_masterFromUtf8
    masterFromUtf8_pre_setPC
    masterFromUtf8_outcome_setPC
    keepFsTrace_realFromUtf8Fallback_master_ok

/-- Master `HookOk` of `fromUtf8GhostHookK` for `fromUtf8SpecK keep masterFromUtf8Spec` on any
    hook-free `P_sub` holding `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem fromUtf8GhostHookK_masterK_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep masterFromUtf8Spec) :=
  hookOk_linkedCallHookG_roTable hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterFromUtf8K_of_hasWords keep hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8K keep)
    (specPreservesFsTrace_masterFromUtf8K keep)
    (masterFromUtf8K_pre_setPC keep)
    (masterFromUtf8K_outcome_setPC keep)
    (keepFsTrace_realFromUtf8Fallback_masterK_ok keep)

section GenericHookOkSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {pl : Placement}
  (hpl : fromUtf8Block.Placeable pl)
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
  (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))

include hpl hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem fromUtf8GhostHook_ascii_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8AsciiSpec stk) :=
  hookOk_fromUtf8Ascii_of_master
    (fromUtf8GhostHook_master_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHook_ascii_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      ((fromUtf8AsciiSpec stk).keepsFs) :=
  hookOk_fromUtf8Ascii_keepsFs_of_master
    (fromUtf8GhostHook_master_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHook_cliFromUtf8_ok :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base) fromUtf8Spec :=
  hookOk_cliFromUtf8_of_master
    (fromUtf8GhostHook_master_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_cliFromUtf8_keepsFs_ok :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      fromUtf8Spec.keepsFs :=
  hookOk_cliFromUtf8_keepsFs_of_master
    (fromUtf8GhostHook_master_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_asciiRO_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8AsciiSpecRO stk) :=
  hookOk_fromUtf8AsciiRO_of_master
    (fromUtf8GhostHook_master_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHook_asciiRO_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      ((fromUtf8AsciiSpecRO stk).keepsFs) :=
  hookOk_fromUtf8AsciiRO_keepsFs_of_master
    (fromUtf8GhostHook_master_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHook_ascii_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withVmPreserved (fromUtf8AsciiSpec stk)) :=
  hookOk_withVmPreserved
    (fromUtf8GhostHook_ascii_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHook_vmPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_ascii_vmPreserved_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withVmPreserved (fromUtf8AsciiSpec stk)).keepsFs :=
  (fromUtf8GhostHook_ascii_vmPreserved_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (fromUtf8GhostHook_fs (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)

theorem fromUtf8GhostHook_cliFromUtf8_vmPreserved_ok :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withVmPreserved fromUtf8Spec) :=
  hookOk_withVmPreserved
    (fromUtf8GhostHook_cliFromUtf8_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (fromUtf8GhostHook_vmPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_asciiRO_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withVmPreserved (fromUtf8AsciiSpecRO stk)) :=
  hookOk_withVmPreserved
    (fromUtf8GhostHook_asciiRO_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHook_vmPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_asciiRO_vmPreserved_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withVmPreserved (fromUtf8AsciiSpecRO stk)).keepsFs :=
  (fromUtf8GhostHook_asciiRO_vmPreserved_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (fromUtf8GhostHook_fs (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)

theorem fromUtf8GhostHook_ascii_oomPool_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withOomPoolPreserved (fromUtf8AsciiSpec stk)) :=
  hookOk_withOomPoolPreserved
    (fromUtf8GhostHook_ascii_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHook_oomPoolPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_asciiRO_oomPool_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (withOomPoolPreserved (fromUtf8AsciiSpecRO stk)) :=
  hookOk_withOomPoolPreserved
    (fromUtf8GhostHook_asciiRO_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHook_oomPoolPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHook_ascii_inImage_ok (img : Obj.Image) (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      ((fromUtf8AsciiSpec stk).inImage img) :=
  hookOk_of_specSimulates (specSimulates_inImage _ img)
    (fromUtf8GhostHook_ascii_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)

theorem fromUtf8GhostHook_asciiRO_inImage_ok (img : Obj.Image) (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      ((fromUtf8AsciiSpecRO stk).inImage img) :=
  hookOk_of_specSimulates (specSimulates_inImage _ img)
    (fromUtf8GhostHook_asciiRO_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)

theorem fromUtf8GhostHookK_asciiK_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (fromUtf8AsciiSpec stk)) :=
  hookOk_fromUtf8AsciiK_of_master keep
    (fromUtf8GhostHookK_masterK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHookK_asciiK_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep ((fromUtf8AsciiSpec stk).keepsFs)) :=
  hookOk_fromUtf8AsciiK_keepsFs_of_master keep
    (fromUtf8GhostHookK_masterK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHookK_cliFromUtf8K_ok :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep fromUtf8Spec) :=
  hookOk_cliFromUtf8K_of_master keep
    (fromUtf8GhostHookK_masterK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHookK_asciiROK_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (fromUtf8AsciiSpecRO stk)) :=
  hookOk_fromUtf8AsciiROK_of_master keep
    (fromUtf8GhostHookK_masterK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHookK_asciiROK_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep ((fromUtf8AsciiSpecRO stk).keepsFs)) :=
  hookOk_fromUtf8AsciiROK_keepsFs_of_master keep
    (fromUtf8GhostHookK_masterK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords) stk

theorem fromUtf8GhostHookK_asciiK_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withVmPreserved (fromUtf8AsciiSpec stk))) := by
  rw [← fromUtf8SpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (fromUtf8GhostHookK_asciiK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHookK_vmPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHookK_asciiK_vmPreserved_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withVmPreserved (fromUtf8AsciiSpec stk)).keepsFs) := by
  rw [← fromUtf8SpecK_keepsFs]
  exact (fromUtf8GhostHookK_asciiK_vmPreserved_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (fromUtf8GhostHookK_fs (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)

theorem fromUtf8GhostHookK_cliFromUtf8K_vmPreserved_ok :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withVmPreserved fromUtf8Spec)) := by
  rw [← fromUtf8SpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (fromUtf8GhostHookK_cliFromUtf8K_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)
    (fromUtf8GhostHookK_vmPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHookK_asciiROK_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withVmPreserved (fromUtf8AsciiSpecRO stk))) := by
  rw [← fromUtf8SpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (fromUtf8GhostHookK_asciiROK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHookK_vmPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHookK_asciiROK_vmPreserved_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withVmPreserved (fromUtf8AsciiSpecRO stk)).keepsFs) := by
  rw [← fromUtf8SpecK_keepsFs]
  exact (fromUtf8GhostHookK_asciiROK_vmPreserved_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords
    stk).keepsFs (fromUtf8GhostHookK_fs (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)

theorem fromUtf8GhostHookK_asciiK_oomPool_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withOomPoolPreserved (fromUtf8AsciiSpec stk))) := by
  rw [← fromUtf8SpecK_withOomPoolPreserved]
  exact hookOk_withOomPoolPreserved
    (fromUtf8GhostHookK_asciiK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHookK_oomPoolPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

theorem fromUtf8GhostHookK_asciiROK_oomPool_ok (stk : Nat := extHookStack) :
    HookOk (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base)
      (fromUtf8SpecK keep (withOomPoolPreserved (fromUtf8AsciiSpecRO stk))) := by
  rw [← fromUtf8SpecK_withOomPoolPreserved]
  exact hookOk_withOomPoolPreserved
    (fromUtf8GhostHookK_asciiROK_ok hpl hsvc_real hsvc_sub hreal_no hsub_no hwords stk)
    (fromUtf8GhostHookK_oomPoolPreserved hpl hsvc_real hsvc_sub hreal_no hsub_no hwords)

end GenericHookOkSuite

theorem fromUtf8GhostHook_any_specK_ok
    (keep_any : BitVec 64 → Bool) {f : State → State} {α : Type} {spec : Spec α}
    (hh : HookOk f spec) : HookOk f (fromUtf8SpecK keep_any spec) :=
  hookOk_memsetSpecK_of_plain keep_any hh

section EmptyHookOkForwarding

variable (keep : BitVec 64 → Bool) {pl : Placement} (hpl : fromUtf8Block.Placeable pl)

include hpl

theorem emptyFromUtf8GhostHook_master_ok :
    HookOk (emptyFromUtf8GhostHook keep pl) masterFromUtf8Spec :=
  fromUtf8GhostHook_master_ok hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl)

theorem emptyFromUtf8GhostHookK_masterK_ok :
    HookOk (emptyFromUtf8GhostHookK keep pl) (fromUtf8SpecK keep masterFromUtf8Spec) :=
  fromUtf8GhostHookK_masterK_ok hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl)

theorem emptyFromUtf8GhostHook_ascii_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (fromUtf8AsciiSpec stk) :=
  hookOk_fromUtf8Ascii_of_master (emptyFromUtf8GhostHook_master_ok keep hpl) stk

theorem emptyFromUtf8GhostHook_ascii_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) ((fromUtf8AsciiSpec stk).keepsFs) :=
  hookOk_fromUtf8Ascii_keepsFs_of_master (emptyFromUtf8GhostHook_master_ok keep hpl) stk

theorem emptyFromUtf8GhostHook_cliFromUtf8_ok :
    HookOk (emptyFromUtf8GhostHook keep pl) fromUtf8Spec :=
  hookOk_cliFromUtf8_of_master (emptyFromUtf8GhostHook_master_ok keep hpl)

theorem emptyFromUtf8GhostHook_asciiRO_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (fromUtf8AsciiSpecRO stk) :=
  hookOk_fromUtf8AsciiRO_of_master (emptyFromUtf8GhostHook_master_ok keep hpl) stk

theorem emptyFromUtf8GhostHook_asciiRO_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) ((fromUtf8AsciiSpecRO stk).keepsFs) :=
  hookOk_fromUtf8AsciiRO_keepsFs_of_master (emptyFromUtf8GhostHook_master_ok keep hpl) stk

theorem emptyFromUtf8GhostHook_ascii_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (withVmPreserved (fromUtf8AsciiSpec stk)) :=
  hookOk_withVmPreserved (emptyFromUtf8GhostHook_ascii_ok keep hpl stk)
    (emptyFromUtf8GhostHook_vmPreserved keep hpl)

theorem emptyFromUtf8GhostHook_ascii_vmPreserved_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (withVmPreserved (fromUtf8AsciiSpec stk)).keepsFs :=
  (emptyFromUtf8GhostHook_ascii_vmPreserved_ok keep hpl stk).keepsFs
    (emptyFromUtf8GhostHook_fs keep pl)

theorem emptyFromUtf8GhostHook_cliFromUtf8_vmPreserved_ok :
    HookOk (emptyFromUtf8GhostHook keep pl) (withVmPreserved fromUtf8Spec) :=
  hookOk_withVmPreserved (emptyFromUtf8GhostHook_cliFromUtf8_ok keep hpl)
    (emptyFromUtf8GhostHook_vmPreserved keep hpl)

theorem emptyFromUtf8GhostHook_asciiRO_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (withVmPreserved (fromUtf8AsciiSpecRO stk)) :=
  hookOk_withVmPreserved (emptyFromUtf8GhostHook_asciiRO_ok keep hpl stk)
    (emptyFromUtf8GhostHook_vmPreserved keep hpl)

theorem emptyFromUtf8GhostHook_asciiRO_vmPreserved_keepsFs_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (withVmPreserved (fromUtf8AsciiSpecRO stk)).keepsFs :=
  (emptyFromUtf8GhostHook_asciiRO_vmPreserved_ok keep hpl stk).keepsFs
    (emptyFromUtf8GhostHook_fs keep pl)

theorem emptyFromUtf8GhostHook_ascii_oomPool_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (withOomPoolPreserved (fromUtf8AsciiSpec stk)) :=
  hookOk_withOomPoolPreserved (emptyFromUtf8GhostHook_ascii_ok keep hpl stk)
    (emptyFromUtf8GhostHook_oomPoolPreserved keep hpl)

theorem emptyFromUtf8GhostHook_asciiRO_oomPool_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHook keep pl) (withOomPoolPreserved (fromUtf8AsciiSpecRO stk)) :=
  hookOk_withOomPoolPreserved (emptyFromUtf8GhostHook_asciiRO_ok keep hpl stk)
    (emptyFromUtf8GhostHook_oomPoolPreserved keep hpl)

theorem emptyFromUtf8GhostHookK_asciiK_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHookK keep pl) (fromUtf8SpecK keep (fromUtf8AsciiSpec stk)) :=
  hookOk_fromUtf8AsciiK_of_master keep (emptyFromUtf8GhostHookK_masterK_ok keep hpl) stk

theorem emptyFromUtf8GhostHookK_asciiK_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHookK keep pl)
      (fromUtf8SpecK keep (withVmPreserved (fromUtf8AsciiSpec stk))) := by
  rw [← fromUtf8SpecK_withVmPreserved]
  exact hookOk_withVmPreserved (emptyFromUtf8GhostHookK_asciiK_ok keep hpl stk)
    (emptyFromUtf8GhostHookK_vmPreserved keep hpl)

theorem emptyFromUtf8GhostHookK_asciiROK_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHookK keep pl) (fromUtf8SpecK keep (fromUtf8AsciiSpecRO stk)) :=
  hookOk_fromUtf8AsciiROK_of_master keep (emptyFromUtf8GhostHookK_masterK_ok keep hpl) stk

theorem emptyFromUtf8GhostHookK_asciiROK_vmPreserved_ok (stk : Nat := extHookStack) :
    HookOk (emptyFromUtf8GhostHookK keep pl)
      (fromUtf8SpecK keep (withVmPreserved (fromUtf8AsciiSpecRO stk))) := by
  rw [← fromUtf8SpecK_withVmPreserved]
  exact hookOk_withVmPreserved (emptyFromUtf8GhostHookK_asciiROK_ok keep hpl stk)
    (emptyFromUtf8GhostHookK_vmPreserved keep hpl)

end EmptyHookOkForwarding

/-! ## 4. Stock-Safe `StepsVisitedIn` Witnesses & `_roTable_liftVis` Replays -/

/-- Under `roTableGuard` and non-faulting execution, `fromUtf8GhostHook` reaches its output state
    along `h2fsgen_StepsVisitedIn keep P_run (s0.setPC pl.base)` while preserving `ExecFrozen`. -/
theorem fromUtf8GhostHook_visitedIn
    {keep : BitVec 64 → Bool} {P_run P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) {s0 : State}
    (hG : roTableGuard (pl.ρ coreUtf8CharWidthSym) corePlacedData1 s0)
    (hnoex : ∀ msg, (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base s0).status ≠
      .Exception msg)
    (hFr : ExecFrozen s0.mem) (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    h2fsgen_StepsVisitedIn keep P_run (s0.setPC pl.base)
        (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base s0) ∧
      ExecFrozen (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base s0).mem :=
  linkedCallHookG_visitedIn hsvc_run hsvc_sub hrun_no hsub_no
    (roTableGuard_stripS keep pl.base (pl.ρ coreUtf8CharWidthSym) corePlacedData1)
    (subroutine_ok_masterFromUtf8_of_hasWords hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8 keep) specPreservesFsTrace_masterFromUtf8
    masterFromUtf8_pre_setPC masterFromUtf8_outcome_setPC hG
    (linkedCallHookG_activeRealPre_of_noException hnoex) hFr hlr_out hCodeSub

/-- Direct `P_real` `On` replay for `fromUtf8GhostHook` (`P_run = P_real`). -/
theorem ghostExternReplaysOn_fromUtf8GhostHook
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base u).status ≠
        .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base u) ∧
      ExecFrozen
        (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base u).mem ∧
      InvMem (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_real P_sub pl.base u).mem :=
  ghostExternReplaysOn_of_linkedCallHookG_roTable hsvc_real hsvc_sub hreal_no hsub_no
    hreal_stub_none hStub hInvLoaded hInvKf hRoInv
    (subroutine_ok_masterFromUtf8_of_hasWords hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8 keep) specPreservesFsTrace_masterFromUtf8
    masterFromUtf8_pre_setPC masterFromUtf8_outcome_setPC

/-- **Stock-safe `StepsVisitedIn` `P_run → P_real` replay for `fromUtf8GhostHook`:**
    Wraps `ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis` so stock-ELF callers discharge
    `hLiftVis` via `h2sl_steps_realW_of_visitedIn_keepSub`. -/
theorem ghostExternReplaysOn_fromUtf8GhostHook_liftVis
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep P_run (u.setPC pl.base) sf → Steps P_real (u.setPC pl.base) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u).status ≠
        .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u) ∧
      ExecFrozen
        (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u).mem ∧
      InvMem (fromUtf8GhostHook (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u).mem :=
  ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis hsvc_run hsvc_sub hrun_no hsub_no
    hreal_stub_none hStub hLiftVis hInvLoaded hInvKf hRoInv
    (subroutine_ok_masterFromUtf8_of_hasWords hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8 keep) specPreservesFsTrace_masterFromUtf8
    masterFromUtf8_pre_setPC masterFromUtf8_outcome_setPC

/-- **Stock-safe `StepsVisitedIn` `P_run → P_real` replay for `fromUtf8GhostHookK`:**
    Wraps `ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis` on `fromUtf8SpecK`. -/
theorem ghostExternReplaysOn_fromUtf8GhostHookK_liftVis
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep P_run (u.setPC pl.base) sf → Steps P_real (u.setPC pl.base) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u).status ≠
        .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u) ∧
      ExecFrozen
        (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u).mem ∧
      InvMem (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base u).mem :=
  ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis hsvc_run hsvc_sub hrun_no hsub_no
    hreal_stub_none hStub hLiftVis hInvLoaded hInvKf hRoInv
    (subroutine_ok_masterFromUtf8K_of_hasWords keep hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8K keep) (specPreservesFsTrace_masterFromUtf8K keep)
    (masterFromUtf8K_pre_setPC keep) (masterFromUtf8K_outcome_setPC keep)

/-- **Ready-to-call `W`-independent `emptyFromUtf8GhostHook` `_liftVis` replay (`P_run = emptyStdProg`):**
    Discharges all `P_run`/`P_sub` side obligations automatically from `hpl : fromUtf8Block.Placeable pl`. -/
theorem ghostExternReplaysOn_emptyFromUtf8GhostHook_liftVis
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_real : Program}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC pl.base) sf →
      Steps P_real (u.setPC pl.base) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (emptyFromUtf8GhostHook keep pl u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (emptyFromUtf8GhostHook keep pl u) ∧
      ExecFrozen (emptyFromUtf8GhostHook keep pl u).mem ∧
      InvMem (emptyFromUtf8GhostHook keep pl u).mem :=
  ghostExternReplaysOn_fromUtf8GhostHook_liftVis hpl emptyStdProg_svc (pureWordsProg_svc _ _)
    (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
    (pureWordsProg_fromUtf8_hasWords pl) hreal_stub_none hStub hLiftVis hInvLoaded hInvKf hRoInv

/-- **Ready-to-call `W`-independent `emptyFromUtf8GhostHookK` `_liftVis` replay with zero caller
    `lr` hypothesis:** Discharges `keep (u.readReg64 .lr) = false` automatically from `hnoex`. -/
theorem ghostExternReplaysOn_emptyFromUtf8GhostHookK_autoLr_liftVis
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_real : Program}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC pl.base) sf →
      Steps P_real (u.setPC pl.base) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (emptyFromUtf8GhostHookK keep pl u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (emptyFromUtf8GhostHookK keep pl u) ∧
      ExecFrozen (emptyFromUtf8GhostHookK keep pl u).mem ∧
      InvMem (emptyFromUtf8GhostHookK keep pl u).mem := by
  have hRep :=
    ghostExternReplaysOn_fromUtf8GhostHookK_liftVis hpl emptyStdProg_svc (pureWordsProg_svc _ _)
      (fun pc _ => emptyStdProg_externAt_none pc) (pureWordsProg_externAt_none _ _)
      (pureWordsProg_fromUtf8_hasWords pl) hreal_stub_none hStub hLiftVis hInvLoaded hInvKf hRoInv
  exact ⟨hRep.1, fun u hpc hrun hnoex hfr hinv =>
    hRep.2 u hpc hrun hnoex hfr (emptyFromUtf8GhostHookK_keepLr_false_of_noException hnoex) hinv⟩

/-- Single-stub `GhostExternReplaysS` packager for `emptyFromUtf8GhostHook` via `_liftVis`. -/
theorem ghostExternReplaysS_emptyFromUtf8GhostHook_liftVis
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_ghost P_real : Program}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hghost_stub : P_ghost.externAt? stubPc = some (emptyFromUtf8GhostHook keep pl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem → InvMem u.mem → ExecFrozen (f u).mem ∧ InvMem (f u).mem)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC pl.base) sf →
      Steps P_real (u.setPC pl.base) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real :=
  ghostExternReplaysS_of_single_stub hghost_stub hother hreal_pres
    (ghostExternReplaysOn_emptyFromUtf8GhostHook_liftVis hpl hreal_stub_none hStub hLiftVis
      hInvLoaded hInvKf hRoInv)

/-- Trajectory-aware single-stub `GhostExternReplaysOn` packager for `emptyFromUtf8GhostHook` via
    `_liftVis`. -/
theorem ghostExternReplaysOn_single_emptyFromUtf8GhostHook_liftVis
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_ghost P_real : Program} {s0 sf : State}
    {stubPc : BitVec 64} {pl : Placement} (hpl : fromUtf8Block.Placeable pl)
    (hghost_stub : P_ghost.externAt? stubPc = some (emptyFromUtf8GhostHook keep pl))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, Steps P_ghost s0 u → Steps P_ghost (f u) sf → u.pc = pc →
        u.status = .Running → (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvMem u.mem →
        ExecFrozen (f u).mem ∧ InvMem (f u).mem)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc pl.base)
    (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC pl.base) sf →
      Steps P_real (u.setPC pl.base) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m →
      RoDataAt m (pl.ρ coreUtf8CharWidthSym) corePlacedData1) :
    GhostExternReplaysOn keep (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have ⟨hnone, hrep⟩ :=
    ghostExternReplaysOn_emptyFromUtf8GhostHook_liftVis hpl hreal_stub_none hStub hLiftVis
      hInvLoaded hInvKf hRoInv
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother hreal_pres
    ⟨hnone, fun u _ _ hpc hrun hnoex _ hfr hlr hinv => hrep u hpc hrun hnoex hfr hlr hinv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost
