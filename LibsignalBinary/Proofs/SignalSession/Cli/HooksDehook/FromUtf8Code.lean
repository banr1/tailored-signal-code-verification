/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP.StepsProcess
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRO
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRW

/-!
# Region-Local `core::str::converts::from_utf8` Code Verification & Master Spec (`HooksDehook.FromUtf8Code`)

Card **R1-a1** for de-hooking `core::str::converts::from_utf8` (`lsFromUtf8Sym`, `156` AArch64
instruction words = `624` bytes from `VerifiedLibraries.RustStd.coreMultiLib.blockLib 1` — rustup
musl sysroot `core` rlib `Cs2kXltWtc1W`; the CLI's own `core` is `CskxtBwYRO61I`, matching `624` B,
with placed-block byte identity deferred to Card R1-a2 after STOCK commit 1 via reloc-masked
compare + `fetch_rebase_of_patchedWord` / `patchedWord_block_some`; zero stack bytes, reading the
immutable `256`-byte `UTF8_CHAR_WIDTH` table `corePlacedData1` at symbol `coreUtf8CharWidthSym`):

1. **Unified RW/RO Master & Process Specifications (`masterFromUtf8Spec`, `processFromUtf8Spec`):**
   - `masterFromUtf8Spec : Spec FromUtf8Call` unifies read-write (`x.ro = false`, `x.p ↦ₛ x.bs`)
     and read-only (`x.ro = true`, `x.p ↦ᵣ x.bs`) input slices via `bytesAt x.ro x.p x.bs`,
     requires zero stack bytes, preserves the 7 non-memory process fields
     `FromUtf8StatePreserved := MemsetStatePreserved` (so `SpecStripSInvariant keep
     masterFromUtf8Spec` holds definitionally for every `keep`), and produces
     `fromUtf8SretPost x.ret x.p x.bs.length x.b18 x.b20 (runUtf8Validation x.bs)` with
     `onPanic = onExit = onOom = ⌜False⌝`.
   - `processFromUtf8Spec : Spec FromUtf8Call` shares the **exact same precondition** as
     `masterFromUtf8Spec` (`processFromUtf8Spec.pre = masterFromUtf8Spec.pre`) and strengthens
     `post` to full `ProcessFieldsPreserved s0 sf` (including `∀ a, sf.mem.perm a = s0.mem.perm a`),
     enabling `FromUtf8Ghost` to prove pointwise `VmPreserved` across the active real-code branch.
   - The `256`-byte `.rodata` table `corePlacedData1` lives in the state guard
     `roTableGuard tbl corePlacedData1` (`withStateGuard (roTableGuard tbl corePlacedData1) _ =
     withRoData tbl corePlacedData1 _` by `rfl`).

2. **Single-Block Region-Local `subroutine_ok` & Concrete `pureWordsProg` Witnesses:**
   - Combines `pureWordsProg_rawCoreFromUtf8_ok` and `pureWordsProg_rawCoreFromUtf8RO_ok` over the
     single `156`-word `fromUtf8PatchedWords pl` hull (depending only on
     `fromUtf8Block.Placeable pl`, with zero hypotheses on other `coreMultiLib` blocks or any
     trusted placed-lib entry; block identity against the stock ELF comes from the untrusted a2
     card + K3(b)).
   - Lifts via `subroutine_ok_lift_pureWords_process` + `subroutine_ok_withRoData_of_sep` to any
     hook-free `P_sub` satisfying `P_sub.hasWords pl.base (fromUtf8PatchedWords pl)`, plus concrete
     `pureWordsProg` instances (`pureWordsProg_fromUtf8_processFromUtf8_ok`,
     `pureWordsProg_fromUtf8_masterFromUtf8_ok`, `pureWordsProg_fromUtf8_masterFromUtf8K_ok`).

3. **`W`-Independent Computable Fallback (`realFromUtf8Fallback`) & Generic `fromUtf8Hook err`:**
   - `realFromUtf8Fallback : State → State` (`retHook realFromUtf8Body`) evaluates
     `runUtf8Validation` directly on `s.mem.readBytes`, depends on **no** `W : CliHooks`, satisfies
     `processFromUtf8Spec` and `masterFromUtf8Spec` (+ `K`), and unconditionally preserves `fs`,
     `trace`, `VmPreserved`, and `OomPreserved ∧ PoolPreserved`.
   - Also exports generic `fromUtf8Hook err` soundness across all ASCII consumer contracts for
     arbitrary `err` plus the fixed `W`-free instance `defaultFromUtf8Hook`.

4. **`LinkedCallHookG` Side Obligations & Consumer `HookOk` Consequence Lifts:**
   - Proves `SpecStripSInvariant`, `SpecPreservesFsTrace`, `pre_setPC`, and `outcome_setPC` for
     `masterFromUtf8Spec` and `fromUtf8SpecK keep masterFromUtf8Spec`, and lifts `HookOk` to all
     RW/RO ASCII consumer contracts (`MainHops.fromUtf8AsciiSpec stk`,
     `FromUtf8.fromUtf8AsciiSpec stk`, `CalleesRO.fromUtf8AsciiSpecRO stk`, `CliExt.fromUtf8Spec`,
     `keepsFs`, `withVmPreserved`, `withOomPoolPreserved`, `inImage`, and `K` variants).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code

open Arm64 ProofLib SepProp
open Arm64.Obj (Placement CodeBlock)
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.RustStd (coreUtf8CharWidthSym corePlacedData1 corePlacedData1_length
  Utf8Error runUtf8Validation fromUtf8SretPost utf8ErrorLenAt
  memRegion18_eq sret_tail8_merge memRegion24_eq_fromUtf8Pre)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (fromUtf8Hook)
open CryptoVerification.SignalSession.CliExt (fromUtf8Spec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.Cli.MainHops (fromUtf8Hook_ok)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt satisfies_bytesAt_to_ro)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData withRoDataSep
  SpecSimulates subroutine_ok_withRoData_of_sep)
open LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8 (runUtf8Validation_of_ascii)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO
  memRegion_24_words pointsToBytesRO_lt_addr_space_of_pointsTo64
  fromUtf8Hook_ro_ok fromUtf8Hook_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved memsetSpecK pureWordsProg_externAt_none
  memsetSpecK_keepsFs memsetSpecK_withVmPreserved memsetSpecK_withOomPoolPreserved
  hookOk_memsetSpecK_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  withStateGuard roTableGuard withStateGuard_roTableGuard_eq_withRoData
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  vmPreserved_of_processFieldsPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (
  fromUtf8Block fromUtf8Placement fromUtf8PatchedWords fromUtf8WordsAt
  fromUtf8PatchedWords_ne_nil pureWordsProg_fromUtf8_hasWords
  pureWordsProg_fromUtf8_noSvcMsr
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRO (
  rawCoreFromUtf8ROSpec pureWordsProg_rawCoreFromUtf8RO_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRW (
  rawCoreFromUtf8Spec pureWordsProg_rawCoreFromUtf8_ok
)

/-! ## 1. Master & Process `from_utf8` Specifications (`masterFromUtf8Spec`, `processFromUtf8Spec`) -/

/-- Non-memory process/VM state fields preserved across real `from_utf8` and `realFromUtf8Fallback`
    (reuses `MemsetStatePreserved`: `fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`,
    `physMemAvail`). -/
abbrev FromUtf8StatePreserved : State → State → Prop := MemsetStatePreserved

/-- `K`-route precondition narrowing (`⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s`), reusing
    `memsetSpecK` directly so all `memsetSpecK_*` defeq lemmas apply. -/
abbrev fromUtf8SpecK := @memsetSpecK

theorem stdStatePreserved_eq_processFieldsPreserved (s0 sf : State) :
    StdStatePreserved s0 sf = ProcessFieldsPreserved s0 sf := rfl

theorem FromUtf8StatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : FromUtf8StatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

/-- Ghost argument record for `masterFromUtf8Spec` and `processFromUtf8Spec`, unifying RW
    (`ro = false`, `p ↦ₛ bs`) and RO (`ro = true`, `p ↦ᵣ bs`) input slices. -/
structure FromUtf8Call where
  ro : Bool
  p : BitVec 64
  ret : BitVec 64
  bs : List (BitVec 8)
  b18 : BitVec 16
  b20 : BitVec 32

/-- Master separation-logic contract for `core::str::converts::from_utf8(p, len) -> sret`:
    requires zero stack bytes, unifies RW and RO slices via `bytesAt x.ro x.p x.bs`, preserves
    `FromUtf8StatePreserved s0 sf` (stripped-memory-invariant), and writes exact
    `fromUtf8SretPost x.ret x.p x.bs.length x.b18 x.b20 (runUtf8Validation x.bs)`. -/
@[expose] def masterFromUtf8Spec : Spec FromUtf8Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 x.bs.length ∧
      s0.readReg64 .x8 = x.ret ∧ x.bs.length < 2 ^ 64⌝ ∗
      bytesAt x.ro x.p x.bs ∗
      (memRegion x.ret 18 ∗ ((x.ret + 18#64) ↦₁₆ x.b18) ∗ ((x.ret + 20#64) ↦₃₂ x.b20))
  post := fun x s0 sf =>
    ⌜FromUtf8StatePreserved s0 sf⌝ ∗
      bytesAt x.ro x.p x.bs ∗
      fromUtf8SretPost x.ret x.p x.bs.length x.b18 x.b20 (runUtf8Validation x.bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Full-permission process companion to `masterFromUtf8Spec` with the **exact same precondition**
    and full `ProcessFieldsPreserved s0 sf` (including `∀ a, sf.mem.perm a = s0.mem.perm a`) in
    `post`, used by `FromUtf8Ghost` to prove `VmPreserved` on the active real-code branch. -/
@[expose] def processFromUtf8Spec : Spec FromUtf8Call where
  pre := masterFromUtf8Spec.pre
  post := fun x s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf⌝ ∗
      bytesAt x.ro x.p x.bs ∗
      fromUtf8SretPost x.ret x.p x.bs.length x.b18 x.b20 (runUtf8Validation x.bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem processFromUtf8Spec_pre_eq :
    processFromUtf8Spec.pre = masterFromUtf8Spec.pre := rfl

/-- `withStateGuard (roTableGuard tbl corePlacedData1)` on `masterFromUtf8Spec` is definitionally
    `withRoData tbl corePlacedData1 masterFromUtf8Spec`. -/
theorem withStateGuard_roTableGuard_masterFromUtf8_eq (tbl : BitVec 64) :
    withStateGuard (roTableGuard tbl corePlacedData1) masterFromUtf8Spec =
      withRoData tbl corePlacedData1 masterFromUtf8Spec :=
  withStateGuard_roTableGuard_eq_withRoData tbl corePlacedData1 masterFromUtf8Spec

/-- `withStateGuard (roTableGuard tbl corePlacedData1)` on `processFromUtf8Spec` is definitionally
    `withRoData tbl corePlacedData1 processFromUtf8Spec`. -/
theorem withStateGuard_roTableGuard_processFromUtf8_eq (tbl : BitVec 64) :
    withStateGuard (roTableGuard tbl corePlacedData1) processFromUtf8Spec =
      withRoData tbl corePlacedData1 processFromUtf8Spec :=
  withStateGuard_roTableGuard_eq_withRoData tbl corePlacedData1 processFromUtf8Spec

/-! ## 2. Single-Block Region-Local `subroutine_ok` & Concrete `pureWordsProg` Witnesses -/

private theorem corePlacedData1_length_le : corePlacedData1.length ≤ 2 ^ 64 := by
  rw [corePlacedData1_length]
  decide

/-- Raw memory-independent separating-`.rodata` spec unifying `rawCoreFromUtf8Spec` (`ro = false`)
    and `rawCoreFromUtf8ROSpec` (`ro = true`), ready for `subroutine_ok_lift_pureWords_process`. -/
private def rawMasterSepSpec (tbl : BitVec 64) : Spec FromUtf8Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 x.bs.length ∧
      s0.readReg64 .x8 = x.ret ∧ x.bs.length < 2 ^ 64⌝ ∗
      (bytesAt x.ro x.p x.bs ∗ (tbl ↦ᵣ corePlacedData1)) ∗
      (memRegion x.ret 18 ∗ ((x.ret + 18#64) ↦₁₆ x.b18) ∗ ((x.ret + 20#64) ↦₃₂ x.b20))
  post := fun x _s0 _sf =>
    (bytesAt x.ro x.p x.bs ∗ (tbl ↦ᵣ corePlacedData1)) ∗
      fromUtf8SretPost x.ret x.p x.bs.length x.b18 x.b20 (runUtf8Validation x.bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem pureWordsProg_rawMasterSep_ok {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl) :
    subroutine_ok (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base
      (rawMasterSepSpec (pl.ρ coreUtf8CharWidthSym)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ro, p, ret, bs, b18, b20⟩ R s0 hpc hrun hpre hsp _hL
  cases ro
  · exact (pureWordsProg_rawCoreFromUtf8_ok hpl).mono_outcome
      (p, ret, bs, b18, b20) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  · exact (pureWordsProg_rawCoreFromUtf8RO_ok hpl).mono_outcome
      (p, ret, bs, b18, b20) R s0 hpc hrun hpre hsp (fun _ hout => hout)

/-- Separating `.rodata` region-local `subroutine_ok` for `processFromUtf8Spec` on any hook-free
    `P_sub` holding the `156` words `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem subroutine_ok_processFromUtf8_roSep_of_hasWords
    {P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    subroutine_ok P_sub pl.base
      (withRoDataSep (pl.ρ coreUtf8CharWidthSym) corePlacedData1 processFromUtf8Spec) := by
  have hproc := subroutine_ok_lift_pureWords_process
    (pureWordsProg_rawMasterSep_ok hpl)
    (pureWordsProg_fromUtf8_noSvcMsr pl)
    hwords hsub_no
    (h_ne := fromUtf8PatchedWords_ne_nil pl)
    (h_pre_mem := fun _ s _ => by cases s; rfl)
    (h_post_mem := fun _ s0 sf _ _ => by cases s0; cases sf; rfl)
  refine (SpecSimulates.of_map ?_).subroutine_ok hproc
  intro x R s0 hpre
  refine ⟨x, R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [withRoDataSep, processFromUtf8Spec, masterFromUtf8Spec, rawMasterSepSpec] at hpre ⊢
    exact Satisfies.mono (by sep_entail) hpre
  · dsimp only [withRoDataSep, processFromUtf8Spec, rawMasterSepSpec] at hpost ⊢
    exact Satisfies.mono (by sep_entail) hpost

/-- Region-local `subroutine_ok` for `withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1
    processFromUtf8Spec` on any hook-free `P_sub` holding `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem subroutine_ok_processFromUtf8_of_hasWords
    {P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    subroutine_ok P_sub pl.base
      (withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1 processFromUtf8Spec) :=
  subroutine_ok_withRoData_of_sep corePlacedData1_length_le
    (subroutine_ok_processFromUtf8_roSep_of_hasWords hpl hsub_no hwords)

/-- Region-local `subroutine_ok` for `withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1
    masterFromUtf8Spec` on any hook-free `P_sub` holding `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem subroutine_ok_masterFromUtf8_of_hasWords
    {P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    subroutine_ok P_sub pl.base
      (withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1 masterFromUtf8Spec) := by
  refine (SpecSimulates.of_map ?_).subroutine_ok
    (subroutine_ok_processFromUtf8_of_hasWords hpl hsub_no hwords)
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [withRoData, processFromUtf8Spec, masterFromUtf8Spec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨FromUtf8StatePreserved.of_processFieldsPreserved hpost.1, hpost.2⟩

/-- Region-local `subroutine_ok` for `withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1
    (fromUtf8SpecK keep masterFromUtf8Spec)` on any hook-free `P_sub` holding
    `fromUtf8PatchedWords pl` at `pl.base`. -/
theorem subroutine_ok_masterFromUtf8K_of_hasWords
    (keep : BitVec 64 → Bool) {P_sub : Program} {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    subroutine_ok P_sub pl.base
      (withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1
        (fromUtf8SpecK keep masterFromUtf8Spec)) := by
  refine (SpecSimulates.of_map ?_).subroutine_ok
    (subroutine_ok_masterFromUtf8_of_hasWords hpl hsub_no hwords)
  intro x R s0 hpre
  dsimp only [withRoData, fromUtf8SpecK, memsetSpecK] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre'⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  refine ⟨x, R, ?_, fun sf _ _ hpost => hpost⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hro, hpre'.2⟩

/-- Concrete single-block `pureWordsProg` instance for `processFromUtf8Spec`. -/
theorem pureWordsProg_fromUtf8_processFromUtf8_ok {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl) :
    subroutine_ok (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base
      (withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1 processFromUtf8Spec) :=
  subroutine_ok_processFromUtf8_of_hasWords hpl
    (pureWordsProg_externAt_none pl.base (fromUtf8PatchedWords pl))
    (pureWordsProg_fromUtf8_hasWords pl)

/-- Concrete single-block `pureWordsProg` instance for `masterFromUtf8Spec`. -/
theorem pureWordsProg_fromUtf8_masterFromUtf8_ok {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl) :
    subroutine_ok (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base
      (withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1 masterFromUtf8Spec) :=
  subroutine_ok_masterFromUtf8_of_hasWords hpl
    (pureWordsProg_externAt_none pl.base (fromUtf8PatchedWords pl))
    (pureWordsProg_fromUtf8_hasWords pl)

/-- Concrete single-block `pureWordsProg` instance for `fromUtf8SpecK keep masterFromUtf8Spec`. -/
theorem pureWordsProg_fromUtf8_masterFromUtf8K_ok (keep : BitVec 64 → Bool) {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl) :
    subroutine_ok (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base
      (withRoData (pl.ρ coreUtf8CharWidthSym) corePlacedData1
        (fromUtf8SpecK keep masterFromUtf8Spec)) :=
  subroutine_ok_masterFromUtf8K_of_hasWords keep hpl
    (pureWordsProg_externAt_none pl.base (fromUtf8PatchedWords pl))
    (pureWordsProg_fromUtf8_hasWords pl)

theorem fromUtf8Placement_rho_table (entry tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) :
    (fromUtf8Placement entry tbl relax1).ρ coreUtf8CharWidthSym = tbl := by
  simp [fromUtf8Placement]

/-- `(entry, tbl, relax1)`-parameterized `subroutine_ok` for `processFromUtf8Spec` on any hook-free
    `P_sub` holding `fromUtf8WordsAt entry tbl relax1` at `entry`. -/
theorem subroutine_ok_processFromUtf8_at
    {P_sub : Program} {entry tbl : BitVec 64} {relax1 : Nat → Bool}
    (hpl : fromUtf8Block.Placeable (fromUtf8Placement entry tbl relax1))
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry (fromUtf8WordsAt entry tbl relax1)) :
    subroutine_ok P_sub entry (withRoData tbl corePlacedData1 processFromUtf8Spec) := by
  have h := subroutine_ok_processFromUtf8_of_hasWords hpl hsub_no hwords
  rwa [fromUtf8Placement_rho_table entry tbl relax1] at h

/-- `(entry, tbl, relax1)`-parameterized `subroutine_ok` for `masterFromUtf8Spec` on any hook-free
    `P_sub` holding `fromUtf8WordsAt entry tbl relax1` at `entry`. -/
theorem subroutine_ok_masterFromUtf8_at
    {P_sub : Program} {entry tbl : BitVec 64} {relax1 : Nat → Bool}
    (hpl : fromUtf8Block.Placeable (fromUtf8Placement entry tbl relax1))
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry (fromUtf8WordsAt entry tbl relax1)) :
    subroutine_ok P_sub entry (withRoData tbl corePlacedData1 masterFromUtf8Spec) := by
  have h := subroutine_ok_masterFromUtf8_of_hasWords hpl hsub_no hwords
  rwa [fromUtf8Placement_rho_table entry tbl relax1] at h

/-- `(entry, tbl, relax1)`-parameterized `subroutine_ok` for `fromUtf8SpecK keep masterFromUtf8Spec`
    on any hook-free `P_sub` holding `fromUtf8WordsAt entry tbl relax1` at `entry`. -/
theorem subroutine_ok_masterFromUtf8K_at (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry tbl : BitVec 64} {relax1 : Nat → Bool}
    (hpl : fromUtf8Block.Placeable (fromUtf8Placement entry tbl relax1))
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry (fromUtf8WordsAt entry tbl relax1)) :
    subroutine_ok P_sub entry
      (withRoData tbl corePlacedData1 (fromUtf8SpecK keep masterFromUtf8Spec)) := by
  have h := subroutine_ok_masterFromUtf8K_of_hasWords keep hpl hsub_no hwords
  rwa [fromUtf8Placement_rho_table entry tbl relax1] at h

/-! ## 3. `W`-Independent Fallback (`realFromUtf8Fallback`) & Generic `fromUtf8Hook err` Soundness -/

/-- Tag byte (`+16`) of `Result::<&str, Utf8Error>::Err`: `1#8` for `Some(_)`, `0#8` for `None`. -/
@[expose] def utf8ErrTag8 (o : Option (BitVec 8)) : BitVec 8 :=
  match o with
  | some _ => 1#8
  | none => 0#8

/-- Payload byte (`+17`) of `Result::<&str, Utf8Error>::Err`: `k` for `Some(k)`, `0#8` for `None`. -/
@[expose] def utf8ErrPay8 (o : Option (BitVec 8)) : BitVec 8 :=
  match o with
  | some k => k
  | none => 0#8

/-- Memory-updating body of `realFromUtf8Fallback`: evaluates `runUtf8Validation` on
    `s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat` and writes the exact 24-byte (`.ok`)
    or 18-byte (`.error`) `Result<&str, Utf8Error>` layout at `s.readReg64 .x8`. Pure, computable,
    and completely independent of `W : CliHooks`. -/
@[expose] def realFromUtf8Body (s : State) : State :=
  let p := s.readReg64 .x0
  let lenBv := s.readReg64 .x1
  let ret := s.readReg64 .x8
  let bs := s.mem.readBytes p lenBv.toNat
  let m' := match runUtf8Validation bs with
    | .ok () =>
      ((s.mem.write64 ret 0#64).write64 (ret + 8#64) p).write64 (ret + 16#64) lenBv
    | .error e =>
      (((s.mem.write64 ret 1#64).write64 (ret + 8#64)
        (BitVec.ofNat 64 e.valid_up_to)).write8 (ret + 16#64)
        (utf8ErrTag8 e.error_len)).write8 (ret + 17#64) (utf8ErrPay8 e.error_len)
  s.setMem m'

/-- `W`-independent computable fallback hook for `from_utf8` (`retHook realFromUtf8Body`), meeting
    both `processFromUtf8Spec` and `masterFromUtf8Spec` without any `W : CliHooks` parameter. -/
@[expose] def realFromUtf8Fallback : State → State :=
  retHook realFromUtf8Body

private theorem realFromUtf8Body_perm_eq (s : State) :
    (realFromUtf8Body s).mem.perm = s.mem.perm := by
  unfold realFromUtf8Body
  dsimp only [State.setMem]
  split
  · simp only [Memory.perm_write64]
  · simp only [Memory.perm_write8, Memory.perm_write64]

theorem realFromUtf8Fallback_processFieldsPreserved (s : State) :
    ProcessFieldsPreserved s (realFromUtf8Fallback s) := by
  refine ⟨by cases s; rfl, by cases s; rfl, by cases s; rfl, by cases s; rfl,
    by cases s; rfl, by cases s; rfl, by cases s; rfl, fun a => ?_⟩
  have hmem : (realFromUtf8Fallback s).mem = (realFromUtf8Body s).mem := by
    cases s; rfl
  rw [hmem]
  exact congrFun (realFromUtf8Body_perm_eq s) a

theorem realFromUtf8Fallback_fs (s : State) :
    (realFromUtf8Fallback s).fs = s.fs := by
  cases s; rfl

theorem realFromUtf8Fallback_trace (s : State) :
    (realFromUtf8Fallback s).trace = s.trace := by
  cases s; rfl

theorem keepFsTrace_realFromUtf8Fallback_eq_apply (s : State) :
    keepFsTrace realFromUtf8Fallback s = realFromUtf8Fallback s := by
  cases s; rfl

theorem keepFsTrace_realFromUtf8Fallback_eq :
    keepFsTrace realFromUtf8Fallback = realFromUtf8Fallback :=
  funext keepFsTrace_realFromUtf8Fallback_eq_apply

theorem realFromUtf8Fallback_fsT :
    HookFsTraced IsFsC realFromUtf8Fallback :=
  fun s => FsTraced.of_eq (realFromUtf8Fallback_trace s)
    (congrArg FsState.files (realFromUtf8Fallback_fs s))

theorem realFromUtf8Fallback_vmPreserved (s : State) :
    VmPreserved s (realFromUtf8Fallback s) :=
  vmPreserved_of_processFieldsPreserved (realFromUtf8Fallback_processFieldsPreserved s)

theorem realFromUtf8Fallback_oomPoolPreserved (s : State) :
    OomPreserved s (realFromUtf8Fallback s) ∧ PoolPreserved s (realFromUtf8Fallback s) := by
  have h := realFromUtf8Fallback_processFieldsPreserved s
  exact ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

/-- `realFromUtf8Fallback` satisfies `processFromUtf8Spec` (both RW and RO slices, both `.ok` and
    `.error` outcomes, with full `ProcessFieldsPreserved`). -/
theorem realFromUtf8Fallback_processFromUtf8_ok :
    HookOk realFromUtf8Fallback processFromUtf8Spec := by
  refine retHook_ok fun ⟨ro, p, ret, bs, b18, b20⟩ R s0 hrun hpre _hsp => ?_
  dsimp only [processFromUtf8Spec, masterFromUtf8Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩
  have hle : bs.length ≤ 2 ^ 64 := Nat.le_of_lt hlen
  have hmem_ro : s0.mem ⊨ (p ↦ᵣ bs) ∗
      ((memRegion ret 18 ∗ ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20)) ∗ R) := by
    rw [sepConj_assoc] at hmem
    exact satisfies_bytesAt_to_ro hmem
  have hread : s0.mem.readBytes p bs.length = bs :=
    (IsBlockRO.pointsToBytesRO p bs hle).read hmem_ro
  have hlen_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  rw [memRegion18_eq ret] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨s17, s16, s_w8, s_w0, hmem⟩
  unfold realFromUtf8Body
  dsimp only
  rw [hx0, hx1, hx8, hlen_nat, hread]
  cases hval : runUtf8Validation bs with
  | ok u =>
    cases u
    let w2 : BitVec 64 := b20 ++ (b18 ++ (s17 ++ s16))
    let F : SepProp := bytesAt ro p bs ∗ R
    have h0 : s0.mem ⊨ (ret ↦₆₄ s_w0) ∗ (((ret + 8#64) ↦₆₄ s_w8) ∗ (((ret + 16#64) ↦₆₄ w2) ∗ F)) := by
      dsimp only [F, w2]
      rw [← sret_tail8_merge ret s16 s17 b18 b20]
      exact Satisfies.mono (by sep_entail) hmem
    have hkf1 : s0.mem.KeepsFrozen (s0.mem.write64 ret 0#64) :=
      Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 ret s_w0).canWrite (by decide) h0) 0#64
    have hw1 := IsBlock.write64 (IsBlock.pointsTo64 ret s_w0) h0 0#64
    have h1 : s0.mem.write64 ret 0#64 ⊨
        ((ret + 8#64) ↦₆₄ s_w8) ∗ (((ret + 16#64) ↦₆₄ w2) ∗ ((ret ↦₆₄ 0#64) ∗ F)) :=
      Satisfies.mono (by sep_entail) hw1
    have hkf2 : s0.mem.KeepsFrozen ((s0.mem.write64 ret 0#64).write64 (ret + 8#64) p) :=
      hkf1.trans
        (Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 (ret + 8#64) s_w8).canWrite (by decide) h1) p)
    have hw2 := IsBlock.write64 (IsBlock.pointsTo64 (ret + 8#64) s_w8) h1 p
    have h2 : (s0.mem.write64 ret 0#64).write64 (ret + 8#64) p ⊨
        ((ret + 16#64) ↦₆₄ w2) ∗ ((ret ↦₆₄ 0#64) ∗ (((ret + 8#64) ↦₆₄ p) ∗ F)) :=
      Satisfies.mono (by sep_entail) hw2
    have hkf3 : s0.mem.KeepsFrozen
        (((s0.mem.write64 ret 0#64).write64 (ret + 8#64) p).write64
          (ret + 16#64) (BitVec.ofNat 64 bs.length)) :=
      hkf2.trans (Memory.keepsFrozen_write64
        ((IsBlock.pointsTo64 (ret + 16#64) w2).canWrite (by decide) h2)
        (BitVec.ofNat 64 bs.length))
    have hw3 := IsBlock.write64 (IsBlock.pointsTo64 (ret + 16#64) w2) h2 (BitVec.ofNat 64 bs.length)
    refine ⟨hkf3, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [processFromUtf8Spec, State.setMem]
    rw [hval]
    dsimp only [fromUtf8SretPost]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨realFromUtf8Fallback_processFieldsPreserved s0, ?_⟩
    dsimp only [F] at hw3
    exact Satisfies.mono (by sep_entail) hw3
  | error e =>
    let tag8 : BitVec 8 := utf8ErrTag8 e.error_len
    let pay8 : BitVec 8 := utf8ErrPay8 e.error_len
    let F : SepProp := bytesAt ro p bs ∗ (((ret + 18#64) ↦₁₆ b18) ∗ (((ret + 20#64) ↦₃₂ b20) ∗ R))
    have h0 : s0.mem ⊨
        (ret ↦₆₄ s_w0) ∗ (((ret + 8#64) ↦₆₄ s_w8) ∗
          (((ret + 16#64) ↦₈ s16) ∗ (((ret + 17#64) ↦₈ s17) ∗ F))) := by
      dsimp only [F]
      exact Satisfies.mono (by sep_entail) hmem
    have hkf1 : s0.mem.KeepsFrozen (s0.mem.write64 ret 1#64) :=
      Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 ret s_w0).canWrite (by decide) h0) 1#64
    have hw1 := IsBlock.write64 (IsBlock.pointsTo64 ret s_w0) h0 1#64
    have h1 : s0.mem.write64 ret 1#64 ⊨
        ((ret + 8#64) ↦₆₄ s_w8) ∗ (((ret + 16#64) ↦₈ s16) ∗
          (((ret + 17#64) ↦₈ s17) ∗ ((ret ↦₆₄ 1#64) ∗ F))) :=
      Satisfies.mono (by sep_entail) hw1
    have hkf2 : s0.mem.KeepsFrozen
        ((s0.mem.write64 ret 1#64).write64 (ret + 8#64) (BitVec.ofNat 64 e.valid_up_to)) :=
      hkf1.trans (Memory.keepsFrozen_write64
        ((IsBlock.pointsTo64 (ret + 8#64) s_w8).canWrite (by decide) h1)
        (BitVec.ofNat 64 e.valid_up_to))
    have hw2 := IsBlock.write64 (IsBlock.pointsTo64 (ret + 8#64) s_w8) h1
      (BitVec.ofNat 64 e.valid_up_to)
    have h2 : (s0.mem.write64 ret 1#64).write64 (ret + 8#64) (BitVec.ofNat 64 e.valid_up_to) ⊨
        ((ret + 16#64) ↦₈ s16) ∗ (((ret + 17#64) ↦₈ s17) ∗
          ((ret ↦₆₄ 1#64) ∗ (((ret + 8#64) ↦₆₄ BitVec.ofNat 64 e.valid_up_to) ∗ F))) :=
      Satisfies.mono (by sep_entail) hw2
    have hkf3 : s0.mem.KeepsFrozen
        (((s0.mem.write64 ret 1#64).write64 (ret + 8#64)
          (BitVec.ofNat 64 e.valid_up_to)).write8 (ret + 16#64) tag8) :=
      hkf2.trans (Memory.keepsFrozen_write8
        ((IsBlock.pointsTo8 (ret + 16#64) s16).canWrite (by decide) h2) tag8)
    have hw3 := IsBlock.write8 (IsBlock.pointsTo8 (ret + 16#64) s16) h2 tag8
    have h3 : (((s0.mem.write64 ret 1#64).write64 (ret + 8#64)
        (BitVec.ofNat 64 e.valid_up_to)).write8 (ret + 16#64) tag8) ⊨
        ((ret + 17#64) ↦₈ s17) ∗ ((ret ↦₆₄ 1#64) ∗
          (((ret + 8#64) ↦₆₄ BitVec.ofNat 64 e.valid_up_to) ∗ (((ret + 16#64) ↦₈ tag8) ∗ F))) :=
      Satisfies.mono (by sep_entail) hw3
    have hkf4 : s0.mem.KeepsFrozen
        ((((s0.mem.write64 ret 1#64).write64 (ret + 8#64)
          (BitVec.ofNat 64 e.valid_up_to)).write8 (ret + 16#64) tag8).write8 (ret + 17#64) pay8) :=
      hkf3.trans (Memory.keepsFrozen_write8
        ((IsBlock.pointsTo8 (ret + 17#64) s17).canWrite (by decide) h3) pay8)
    have hw4 := IsBlock.write8 (IsBlock.pointsTo8 (ret + 17#64) s17) h3 pay8
    refine ⟨hkf4, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [processFromUtf8Spec, State.setMem]
    rw [hval]
    dsimp only [fromUtf8SretPost]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨realFromUtf8Fallback_processFieldsPreserved s0, ?_⟩
    dsimp only [F, tag8, pay8] at hw4
    have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
    cases herr : e.error_len with
    | some k =>
      dsimp only [utf8ErrorLenAt]
      rw [ha17]
      rw [herr] at hw4
      dsimp only [utf8ErrTag8, utf8ErrPay8] at hw4
      exact Satisfies.mono (by sep_entail) hw4
    | none =>
      dsimp only [utf8ErrorLenAt]
      rw [ha17]
      rw [herr] at hw4
      dsimp only [utf8ErrTag8, utf8ErrPay8] at hw4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      exact Satisfies.mono (Entails.sepExists_right 0#8 (by sep_entail)) hw4

/-- Transport `HookOk f spec₁` along any `SpecSimulates spec₁ spec₂`. -/
theorem hookOk_of_specSimulates {α β : Type} {f : State → State}
    {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) (hh : HookOk f spec₁) :
    HookOk f spec₂ :=
  LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode.SpecSimulates.hookOk hsim hh

/-- `realFromUtf8Fallback` satisfies `masterFromUtf8Spec`. -/
theorem realFromUtf8Fallback_masterFromUtf8_ok :
    HookOk realFromUtf8Fallback masterFromUtf8Spec := by
  refine hookOk_of_specSimulates (SpecSimulates.of_map ?_) realFromUtf8Fallback_processFromUtf8_ok
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [processFromUtf8Spec, masterFromUtf8Spec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨FromUtf8StatePreserved.of_processFieldsPreserved hpost.1, hpost.2⟩

/-- `realFromUtf8Fallback` satisfies `fromUtf8SpecK keep masterFromUtf8Spec` for every `keep`. -/
theorem realFromUtf8Fallback_masterFromUtf8K_ok (keep : BitVec 64 → Bool) :
    HookOk realFromUtf8Fallback (fromUtf8SpecK keep masterFromUtf8Spec) :=
  hookOk_memsetSpecK_of_plain keep realFromUtf8Fallback_masterFromUtf8_ok

theorem keepFsTrace_realFromUtf8Fallback_master_ok :
    HookOk (keepFsTrace realFromUtf8Fallback) masterFromUtf8Spec := by
  rw [keepFsTrace_realFromUtf8Fallback_eq]
  exact realFromUtf8Fallback_masterFromUtf8_ok

theorem keepFsTrace_realFromUtf8Fallback_masterK_ok (keep : BitVec 64 → Bool) :
    HookOk (keepFsTrace realFromUtf8Fallback) (fromUtf8SpecK keep masterFromUtf8Spec) := by
  rw [keepFsTrace_realFromUtf8Fallback_eq]
  exact realFromUtf8Fallback_masterFromUtf8K_ok keep

/-- Fixed `W`-independent instance of today's idealized `fromUtf8Hook` (for F3 `W`-free witness). -/
@[expose] noncomputable def defaultFromUtf8Hook : State → State :=
  fromUtf8Hook (fun _ => (0#64, 0#16))

/-- Generic `W`-free soundness of `fromUtf8Hook err` on RW `MainHops.fromUtf8AsciiSpec stk` for
    every `err` and every `stk : Nat`. -/
theorem fromUtf8Hook_ascii_ok (stk : Nat)
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookOk (fromUtf8Hook err)
      (CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk) :=
  fromUtf8Hook_ok stk err

/-- Generic `W`-free soundness of `fromUtf8Hook err` on RW `withVmPreserved (fromUtf8AsciiSpec stk)`
    for every `err` and every `stk : Nat`. -/
theorem fromUtf8Hook_ascii_vmPreserved_ok (stk : Nat)
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookOk (fromUtf8Hook err)
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk)) :=
  hookOk_withVmPreserved (fromUtf8Hook_ok stk err) (fromUtf8Hook_vmPreserved err)

/-- Generic `W`-free soundness of `fromUtf8Hook err` on RO `withVmPreserved (fromUtf8AsciiSpecRO stk)`
    for every `err` and every `stk : Nat`. -/
theorem fromUtf8Hook_asciiRO_vmPreserved_ok (stk : Nat)
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookOk (fromUtf8Hook err) (withVmPreserved (fromUtf8AsciiSpecRO stk)) :=
  hookOk_withVmPreserved (fromUtf8Hook_ro_ok stk err) (fromUtf8Hook_vmPreserved err)

/-- Fixed `W`-independent `defaultFromUtf8Hook` soundness on RW `withVmPreserved (fromUtf8AsciiSpec stk)`. -/
theorem defaultFromUtf8Hook_ascii_vmPreserved_ok (stk : Nat) :
    HookOk defaultFromUtf8Hook
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk)) :=
  fromUtf8Hook_ascii_vmPreserved_ok stk (fun _ => (0#64, 0#16))

/-- Fixed `W`-independent `defaultFromUtf8Hook` soundness on RO `withVmPreserved (fromUtf8AsciiSpecRO stk)`. -/
theorem defaultFromUtf8Hook_asciiRO_vmPreserved_ok (stk : Nat) :
    HookOk defaultFromUtf8Hook (withVmPreserved (fromUtf8AsciiSpecRO stk)) :=
  fromUtf8Hook_asciiRO_vmPreserved_ok stk (fun _ => (0#64, 0#16))

/-! ## 4. `LinkedCallHookG` Side Obligations & Generic Consumer `HookOk` Consequence Lifts -/

theorem specStripSInvariant_masterFromUtf8 (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterFromUtf8Spec where
  pre_eq := fun ⟨_, _, _, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterFromUtf8K (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (fromUtf8SpecK keep masterFromUtf8Spec) where
  pre_eq := fun ⟨_, _, _, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterFromUtf8 :
    SpecPreservesFsTrace masterFromUtf8Spec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterFromUtf8Spec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.1
    have htr : sf.trace = s0.trace := hpost.1.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [masterFromUtf8Spec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [masterFromUtf8Spec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [masterFromUtf8Spec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem specPreservesFsTrace_masterFromUtf8K (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (fromUtf8SpecK keep masterFromUtf8Spec) :=
  specPreservesFsTrace_masterFromUtf8

theorem masterFromUtf8_pre_setPC (x : FromUtf8Call) (s : State) (pc : BitVec 64) :
    masterFromUtf8Spec.pre x (s.setPC pc) = masterFromUtf8Spec.pre x s := by
  rcases x with ⟨_, _, _, _, _, _⟩; cases s; rfl

theorem processFromUtf8_pre_setPC (x : FromUtf8Call) (s : State) (pc : BitVec 64) :
    processFromUtf8Spec.pre x (s.setPC pc) = processFromUtf8Spec.pre x s :=
  masterFromUtf8_pre_setPC x s pc

theorem masterFromUtf8K_pre_setPC (keep : BitVec 64 → Bool)
    (x : FromUtf8Call) (s : State) (pc : BitVec 64) :
    (fromUtf8SpecK keep masterFromUtf8Spec).pre x (s.setPC pc) =
      (fromUtf8SpecK keep masterFromUtf8Spec).pre x s := by
  rcases x with ⟨_, _, _, _, _, _⟩; cases s; rfl

theorem masterFromUtf8_outcome_setPC (x : FromUtf8Call) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterFromUtf8Spec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterFromUtf8Spec x R s0 sf := by
  rcases x with ⟨_, _, _, _, _, _⟩; cases s0; cases sf; exact h

theorem masterFromUtf8K_outcome_setPC (keep : BitVec 64 → Bool)
    (x : FromUtf8Call) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (fromUtf8SpecK keep masterFromUtf8Spec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (fromUtf8SpecK keep masterFromUtf8Spec) x R s0 sf := by
  rcases x with ⟨_, _, _, _, _, _⟩; cases s0; cases sf; exact h

/-- Lift any `SpecSimulates spec₁ spec₂` across `fromUtf8SpecK keep`. -/
theorem specSimulates_fromUtf8SpecK (keep : BitVec 64 → Bool) {α β : Type}
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (fromUtf8SpecK keep spec₁) (fromUtf8SpecK keep spec₂) := by
  intro y R s0 hpre
  dsimp only [fromUtf8SpecK, memsetSpecK] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre₁⟩

/-- Any `SpecSimulates` lifts to `.inImage img`. -/
theorem specSimulates_inImage {α : Type} (spec : Spec α) (img : Obj.Image) :
    SpecSimulates spec (spec.inImage img) :=
  LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm.specSimulates_inImage
    img spec

private theorem bytesAt_lt_two_pow_64_of_sep_region24 {m : Memory} {ro : Bool} {p r : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ bytesAt ro p bs ∗ (memRegion r 24 ∗ R)) :
    bs.length < 2 ^ 64 := by
  have hro : m ⊨ (p ↦ᵣ bs) ∗ (memRegion r 24 ∗ R) := satisfies_bytesAt_to_ro h
  rw [memRegion_24_words r] at hro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hro
  rcases hro with ⟨w2, w1, w0, hw⟩
  have hw' : m ⊨ (p ↦ᵣ bs) ∗
      ((r ↦₆₄ w0) ∗ (((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ R))) :=
    Satisfies.mono (by sep_entail) hw
  exact pointsToBytesRO_lt_addr_space_of_pointsTo64 hw'

/-- `MainHops.fromUtf8AsciiSpec stk` and `HookDischarge.RustStd.FromUtf8.fromUtf8AsciiSpec stk`
    are definitionally identical at every `stk : Nat`. -/
theorem mainHops_fromUtf8AsciiSpec_eq_rustStd (stk : Nat) :
    CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk =
      LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8.fromUtf8AsciiSpec stk := rfl

/-- `MainHops.fromUtf8AsciiSpec extHookStack` is definitionally `CliExt.fromUtf8Spec`. -/
theorem mainHops_fromUtf8AsciiSpec_extHookStack :
    CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec extHookStack =
      fromUtf8Spec := rfl

private theorem bytesAt_false (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt false p bs = (p ↦ₛ bs) := rfl

private theorem bytesAt_true (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt true p bs = (p ↦ᵣ bs) := rfl

/-- Forward simulation from `masterFromUtf8Spec` (`ro = false`) to
    `(MainHops.fromUtf8AsciiSpec stk).keepsFs` for every `stk : Nat`. -/
theorem masterFromUtf8_simulates_ascii_keepsFs (stk : Nat) :
    SpecSimulates masterFromUtf8Spec
      ((CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk).keepsFs) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨r, p, bs⟩ R s0 hpre
  dsimp only [Spec.keepsFs,
    CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, hascii⟩, hmem⟩ := hpre
  have hmem_assoc : s0.mem ⊨ bytesAt false p bs ∗ (memRegion r 24 ∗ (stackAt s0.sp stk ∗ R)) := by
    rw [bytesAt_false]
    exact Satisfies.mono (by sep_entail) hmem
  have hlen : bs.length < 2 ^ 64 := bytesAt_lt_two_pow_64_of_sep_region24 hmem_assoc
  rw [memRegion24_eq_fromUtf8Pre r] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨b20, b18, hmem⟩
  refine ⟨⟨false, p, r, bs, b18, b20⟩, stackAt s0.sp stk ∗ R, ?_, ?_⟩
  · dsimp only [masterFromUtf8Spec]
    rw [bytesAt_false, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlen⟩, Satisfies.mono (by sep_entail) hmem⟩
  · intro sf _ _ hpost
    dsimp only [masterFromUtf8Spec] at hpost
    rw [bytesAt_false, runUtf8Validation_of_ascii hascii] at hpost
    dsimp only [fromUtf8SretPost] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hst, hpost⟩ := hpost
    have hfs : sf.fs = s0.fs := hst.1
    have htr : sf.trace = s0.trace := hst.2.1
    dsimp only [Spec.keepsFs,
      CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs⟩, Satisfies.mono (by sep_entail) hpost⟩

/-- Forward simulation from `masterFromUtf8Spec` (`ro = false`) to
    `MainHops.fromUtf8AsciiSpec stk` for every `stk : Nat`. -/
theorem masterFromUtf8_simulates_ascii (stk : Nat) :
    SpecSimulates masterFromUtf8Spec
      (CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk) :=
  (masterFromUtf8_simulates_ascii_keepsFs stk).trans SpecSimulates.drop_keepsFs

/-- Forward simulation from `masterFromUtf8Spec` (`ro = true`) to
    `(fromUtf8AsciiSpecRO stk).keepsFs` for every `stk : Nat`. -/
theorem masterFromUtf8_simulates_asciiRO_keepsFs (stk : Nat) :
    SpecSimulates masterFromUtf8Spec ((fromUtf8AsciiSpecRO stk).keepsFs) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨r, p, bs⟩ R s0 hpre
  dsimp only [Spec.keepsFs, fromUtf8AsciiSpecRO] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, hascii⟩, hmem⟩ := hpre
  have hmem_assoc : s0.mem ⊨ bytesAt true p bs ∗ (memRegion r 24 ∗ (stackAt s0.sp stk ∗ R)) := by
    rw [bytesAt_true]
    exact Satisfies.mono (by sep_entail) hmem
  have hlen : bs.length < 2 ^ 64 := bytesAt_lt_two_pow_64_of_sep_region24 hmem_assoc
  rw [memRegion24_eq_fromUtf8Pre r] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨b20, b18, hmem⟩
  refine ⟨⟨true, p, r, bs, b18, b20⟩, stackAt s0.sp stk ∗ R, ?_, ?_⟩
  · dsimp only [masterFromUtf8Spec]
    rw [bytesAt_true, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlen⟩, Satisfies.mono (by sep_entail) hmem⟩
  · intro sf _ _ hpost
    dsimp only [masterFromUtf8Spec] at hpost
    rw [bytesAt_true, runUtf8Validation_of_ascii hascii] at hpost
    dsimp only [fromUtf8SretPost] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hst, hpost⟩ := hpost
    have hfs : sf.fs = s0.fs := hst.1
    have htr : sf.trace = s0.trace := hst.2.1
    dsimp only [Spec.keepsFs, fromUtf8AsciiSpecRO]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs⟩, Satisfies.mono (by sep_entail) hpost⟩

/-- Forward simulation from `masterFromUtf8Spec` (`ro = true`) to `fromUtf8AsciiSpecRO stk`
    for every `stk : Nat`. -/
theorem masterFromUtf8_simulates_asciiRO (stk : Nat) :
    SpecSimulates masterFromUtf8Spec (fromUtf8AsciiSpecRO stk) :=
  (masterFromUtf8_simulates_asciiRO_keepsFs stk).trans SpecSimulates.drop_keepsFs

/-- Lift `HookOk f masterFromUtf8Spec` to `MainHops.fromUtf8AsciiSpec stk` for any `stk : Nat`. -/
theorem hookOk_fromUtf8Ascii_of_master {f : State → State}
    (hh : HookOk f masterFromUtf8Spec) (stk : Nat := extHookStack) :
    HookOk f (CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk) :=
  hookOk_of_specSimulates (masterFromUtf8_simulates_ascii stk) hh

/-- Lift `HookOk f masterFromUtf8Spec` to `(MainHops.fromUtf8AsciiSpec stk).keepsFs`. -/
theorem hookOk_fromUtf8Ascii_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterFromUtf8Spec) (stk : Nat := extHookStack) :
    HookOk f ((CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk).keepsFs) :=
  hookOk_of_specSimulates (masterFromUtf8_simulates_ascii_keepsFs stk) hh

/-- Lift `HookOk f masterFromUtf8Spec` to `CliExt.fromUtf8Spec` (`stk = extHookStack`). -/
theorem hookOk_cliFromUtf8_of_master {f : State → State}
    (hh : HookOk f masterFromUtf8Spec) :
    HookOk f fromUtf8Spec :=
  hookOk_fromUtf8Ascii_of_master hh extHookStack

/-- Lift `HookOk f masterFromUtf8Spec` to `CliExt.fromUtf8Spec.keepsFs`. -/
theorem hookOk_cliFromUtf8_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterFromUtf8Spec) :
    HookOk f fromUtf8Spec.keepsFs :=
  hookOk_fromUtf8Ascii_keepsFs_of_master hh extHookStack

/-- Lift `HookOk f masterFromUtf8Spec` to `fromUtf8AsciiSpecRO stk` for any `stk : Nat`. -/
theorem hookOk_fromUtf8AsciiRO_of_master {f : State → State}
    (hh : HookOk f masterFromUtf8Spec) (stk : Nat := extHookStack) :
    HookOk f (fromUtf8AsciiSpecRO stk) :=
  hookOk_of_specSimulates (masterFromUtf8_simulates_asciiRO stk) hh

/-- Lift `HookOk f masterFromUtf8Spec` to `(fromUtf8AsciiSpecRO stk).keepsFs` for any `stk : Nat`. -/
theorem hookOk_fromUtf8AsciiRO_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterFromUtf8Spec) (stk : Nat := extHookStack) :
    HookOk f ((fromUtf8AsciiSpecRO stk).keepsFs) :=
  hookOk_of_specSimulates (masterFromUtf8_simulates_asciiRO_keepsFs stk) hh

/-- Lift `HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)` to
    `fromUtf8SpecK keep (MainHops.fromUtf8AsciiSpec stk)`. -/
theorem hookOk_fromUtf8AsciiK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)) (stk : Nat := extHookStack) :
    HookOk f (fromUtf8SpecK keep
      (CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk)) :=
  hookOk_of_specSimulates (specSimulates_fromUtf8SpecK keep (masterFromUtf8_simulates_ascii stk)) hh

/-- Lift `HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)` to
    `fromUtf8SpecK keep ((MainHops.fromUtf8AsciiSpec stk).keepsFs)`. -/
theorem hookOk_fromUtf8AsciiK_keepsFs_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)) (stk : Nat := extHookStack) :
    HookOk f (fromUtf8SpecK keep
      ((CryptoVerification.SignalSession.Cli.MainHops.fromUtf8AsciiSpec stk).keepsFs)) :=
  hookOk_of_specSimulates
    (specSimulates_fromUtf8SpecK keep (masterFromUtf8_simulates_ascii_keepsFs stk)) hh

/-- Lift `HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)` to
    `fromUtf8SpecK keep CliExt.fromUtf8Spec`. -/
theorem hookOk_cliFromUtf8K_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)) :
    HookOk f (fromUtf8SpecK keep fromUtf8Spec) :=
  hookOk_fromUtf8AsciiK_of_master keep hh extHookStack

/-- Lift `HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)` to
    `fromUtf8SpecK keep (fromUtf8AsciiSpecRO stk)`. -/
theorem hookOk_fromUtf8AsciiROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)) (stk : Nat := extHookStack) :
    HookOk f (fromUtf8SpecK keep (fromUtf8AsciiSpecRO stk)) :=
  hookOk_of_specSimulates
    (specSimulates_fromUtf8SpecK keep (masterFromUtf8_simulates_asciiRO stk)) hh

/-- Lift `HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)` to
    `fromUtf8SpecK keep ((fromUtf8AsciiSpecRO stk).keepsFs)`. -/
theorem hookOk_fromUtf8AsciiROK_keepsFs_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (fromUtf8SpecK keep masterFromUtf8Spec)) (stk : Nat := extHookStack) :
    HookOk f (fromUtf8SpecK keep ((fromUtf8AsciiSpecRO stk).keepsFs)) :=
  hookOk_of_specSimulates
    (specSimulates_fromUtf8SpecK keep (masterFromUtf8_simulates_asciiRO_keepsFs stk)) hh

theorem fromUtf8SpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (fromUtf8SpecK keep spec).keepsFs = fromUtf8SpecK keep spec.keepsFs :=
  memsetSpecK_keepsFs keep spec

theorem fromUtf8SpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (fromUtf8SpecK keep spec) = fromUtf8SpecK keep (withVmPreserved spec) :=
  memsetSpecK_withVmPreserved keep spec

theorem fromUtf8SpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (fromUtf8SpecK keep spec) =
      fromUtf8SpecK keep (withOomPoolPreserved spec) :=
  memsetSpecK_withOomPoolPreserved keep spec

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code
