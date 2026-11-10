/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import

/-!
# Closed-`lr` Trap & Subroutine-Outcome `keepFromUtf8Block lr = false` Suite (`HooksDehook.FromUtf8LrTrap`)

Card **R1-d** of the `core::str::converts::from_utf8` de-hook row (`dehook_plan.md` §1, §5 R1-d;
C11 §8.2): proves that inside the 156-word (`624` B) frameless leaf `(coreMultiLib.blockLib 1).text`
under any single-block placement `pl : Obj.Placement` (unrelaxed or linker-relaxed, with the 256 B
`UTF8_CHAR_WIDTH` `.rodata` table outside the executable `TrapRegion`), no execution path writes
`x30` (`lr`) or leaves `[pl.base, pl.base + 624)` except via `ret x30` to `lr`.

Consequently, whenever a ghost run starting with `keepFromUtf8Block pl.base (s0.readReg64 .lr) = false`
terminates without `.Exception`/`.Halted` and (if `.Running`) returns to `s0.readReg64 .lr`, every
intermediate call site `u` satisfies `keepFromUtf8Block pl.base (u.readReg64 .lr) = false`.

## Design & Review-Rule Notes (`REV-S2 F1` and `REV-S2 H1`)
- **Zero `decide` calls:** reuses `TrapSafeWords.fromUtf8_regionWordsSafe` (`TrapSafeWords.lean:1176`)
  directly via `fromUtf8PatchedWords_eq_codeBlockPatchedWords`.
- **`REV-S2 F1` (Entry-Excluded Extern Premise):** on the ghost route, `pl.base` (`lsFromUtf8Sym`)
  is hooked inside `keepFromUtf8Block pl.base` (`keepFromUtf8Block_entry`). Ready-to-apply ghost
  corollaries **never** assume whole-hull `externAt? pc = none`; they take the entry-excluded
  premise `∀ pc, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base → P_ghost.externAt? pc = none`
  (`entries = [pl.base]`), matching STARTUP C2's `f3Row_ghostProg617_externAt_none_of_ne_entry`.
- **`REV-S2 H1` (`CodeLoaded (f u).mem` Post-Hook Variants):** `GhostRowReplayOn.replay_at_stub`
  Arm 2 does **not** supply `P_sub.CodeLoaded s0.mem`; card `c` obtains
  `P_sub.CodeLoaded (f u).mem` from `InvS u` (`P_sub.CodeLoaded u.mem`) +
  `u.mem.KeepsFrozen (f u).mem`. Both `fromUtf8_lr_trap_after_hook_{ret,returned}` and the
  `*_after_hook_of_{outcome,subroutineOutcome}_post` corollaries consume `P_sub.CodeLoaded (f u).mem`
  directly (alongside `s0.mem` wrappers for 1:1 parity with `BcmpLrTrap`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open CryptoVerification.SignalSession (fromUtf8Hook)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace ActiveRealPre)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG linkedCallHookG_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  TrapHook trapHook_of_exception_on_keepLr
  lr_trap_at_call_ret lr_trap_at_call
  TrapEntryGuard keepLr_false_at_stub_of_outcome
  reg_ext_of_entry_excluded reg_ext_forall_of_entry_excluded
  codeBlockPatchedWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (
  lr_trap_after_hook_ret
  keepLr_false_after_hook_of_outcome
  keepLr_false_after_hook_of_subroutineOutcome
  keepLr_false_at_stub_of_subroutineOutcome
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (
  fromUtf8Block fromUtf8Block_code_length
  fromUtf8PatchedWords fromUtf8PatchedWords_length
  pureWordsProg_fromUtf8_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code (
  realFromUtf8Fallback defaultFromUtf8Hook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost (
  keepFromUtf8Block KeepCoversFromUtf8
  fromUtf8GhostHook fromUtf8GhostHookK
  fromUtf8GhostHookPure fromUtf8GhostHookPureK
  emptyFromUtf8GhostHook emptyFromUtf8GhostHookK
  fromUtf8GhostHookK_of_keepLr_true
)

/-! ## 1. Single-Block 624 B `from_utf8` Region, `keep` Alignment, and `RegionWordsSafe` -/

/-- Byte length (`624` = `4 * 156`) of the single-block `core::str::converts::from_utf8` leaf. -/
@[expose] def fromUtf8ByteLen : Nat := 624

theorem fromUtf8ByteLen_eq : fromUtf8ByteLen = 624 := rfl

theorem fromUtf8Block_code_length_eq : fromUtf8Block.code.length = fromUtf8ByteLen :=
  fromUtf8Block_code_length

theorem four_mul_fromUtf8PatchedWords_length (pl : Obj.Placement) :
    4 * (fromUtf8PatchedWords pl).length = fromUtf8ByteLen := by
  rw [fromUtf8PatchedWords_length, fromUtf8ByteLen_eq]

/-- Compatibility alias for `FromUtf8Ghost.keepFromUtf8Block`. -/
abbrev keepFromUtf8Range : BitVec 64 → BitVec 64 → Bool := keepFromUtf8Block

/-- `FromUtf8Ghost.keepFromUtf8Block` is definitionally equal to `TrapSafeWords.keepBlock` of length
    `fromUtf8ByteLen` (`624`). -/
theorem keepFromUtf8Block_eq_keepBlock (entryTarget : BitVec 64) :
    keepFromUtf8Block entryTarget = keepBlock entryTarget fromUtf8ByteLen := rfl

theorem keepFromUtf8Block_iff (entryTarget pc : BitVec 64) :
    keepFromUtf8Block entryTarget pc = true ↔ (pc - entryTarget).toNat < fromUtf8ByteLen := by
  simp [keepFromUtf8Block, fromUtf8ByteLen, decide_eq_true_eq]

/-- The `from_utf8` entry `entryTarget` lies inside `keepFromUtf8Block entryTarget`. -/
theorem keepFromUtf8Block_entry (entryTarget : BitVec 64) :
    keepFromUtf8Block entryTarget entryTarget = true := by
  rw [keepFromUtf8Block_iff, BitVec.sub_self]
  decide

/-- Transport membership in `keepFromUtf8Block entryTarget` into any `keepR` satisfying
    `KeepCoversFromUtf8 keepR entryTarget`. -/
theorem keep_of_keepCoversFromUtf8 {keepR : BitVec 64 → Bool} {entryTarget pc : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR entryTarget)
    (hin : keepFromUtf8Block entryTarget pc = true) :
    keepR pc = true := by
  rw [keepFromUtf8Block_iff, fromUtf8ByteLen_eq] at hin
  have heq : entryTarget + BitVec.ofNat 64 (pc - entryTarget).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rw [← heq]
  exact hcov (pc - entryTarget).toNat hin

/-- Single-block `TrapRegion` for `core::str::converts::from_utf8` under placement `pl`
    (the 256 B `UTF8_CHAR_WIDTH` `.rodata` table is data, not executable code). -/
@[expose] def fromUtf8Region (pl : Obj.Placement) : TrapRegion :=
  [(pl.base, fromUtf8PatchedWords pl)]

/-- `FromUtf8SingleBlock.fromUtf8PatchedWords pl` equals `TrapSafeWords.codeBlockPatchedWords` on
    `fromUtf8Block`. -/
theorem fromUtf8PatchedWords_eq_codeBlockPatchedWords (pl : Obj.Placement) :
    fromUtf8PatchedWords pl = codeBlockPatchedWords fromUtf8Block pl := by
  unfold fromUtf8PatchedWords codeBlockPatchedWords
  rw [fromUtf8Block_code_length]

/-- `keepOf (fromUtf8Region pl)` equals `keepFromUtf8Block pl.base` (independent of `pl.ρ` and
    `pl.relax`). -/
theorem keepOf_fromUtf8Region (pl : Obj.Placement) :
    keepOf (fromUtf8Region pl) = keepFromUtf8Block pl.base := by
  funext pc
  dsimp only [fromUtf8Region]
  rw [keepOf_singleton, four_mul_fromUtf8PatchedWords_length]
  rfl

theorem keepOf_fromUtf8Region_apply (pl : Obj.Placement) (pc : BitVec 64) :
    keepOf (fromUtf8Region pl) pc = keepFromUtf8Block pl.base pc :=
  congrFun (keepOf_fromUtf8Region pl) pc

/-- Placement-generic `RegionWordsSafe` for `fromUtf8Region pl` (reuses S2 M2's
    `TrapSafeWords.fromUtf8_regionWordsSafe` with zero `decide` calls). -/
theorem fromUtf8_regionWordsSafe (pl : Obj.Placement) :
    RegionWordsSafe (fromUtf8Region pl) := by
  unfold fromUtf8Region
  rw [fromUtf8PatchedWords_eq_codeBlockPatchedWords]
  exact LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords.fromUtf8_regionWordsSafe pl

/-- `RegionHasWords [P_sub] (fromUtf8Region pl)` from
    `P_sub.hasWords pl.base (fromUtf8PatchedWords pl)`. -/
theorem fromUtf8Region_hasWords_of_hasWords {P_sub : Program} {pl : Obj.Placement}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) :
    RegionHasWords [P_sub] (fromUtf8Region pl) := by
  intro blk hmem
  rw [fromUtf8Region, List.mem_singleton] at hmem
  subst hmem
  exact ⟨P_sub, List.mem_singleton.mpr rfl, hHas⟩

/-- Unconditional `RegionHasWords` for `pureWordsProg pl.base (fromUtf8PatchedWords pl)`. -/
theorem fromUtf8Region_hasWords_pure (pl : Obj.Placement) :
    RegionHasWords [pureWordsProg pl.base (fromUtf8PatchedWords pl)] (fromUtf8Region pl) :=
  fromUtf8Region_hasWords_of_hasWords (pureWordsProg_fromUtf8_hasWords pl)

theorem fromUtf8Region_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem := by
  constructor
  · intro h
    exact h P_sub (List.mem_singleton.mpr rfl)
  · intro h P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact h

private theorem pureWordsProg_code_length (base : BitVec 64) (ws : List (BitVec 32)) :
    (pureWordsProg base ws).code.length = 4 * ws.length := by
  change (ws.flatMap Program.wordToBytesLE).length = 4 * ws.length
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih]
    change 4 + 4 * rest.length = 4 * (rest.length + 1)
    omega

/-- Discharges `(pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded (stripExecOutside keepR mem)`
    (needed by `FromUtf8Ghost.fromUtf8GhostHook_visitedIn` and `_liftVis` replays) from
    `KeepCoversFromUtf8 keepR pl.base` and `CodeLoaded mem`. -/
theorem fromUtf8_codeLoaded_stripExecOutside {keepR : BitVec 64 → Bool} {pl : Obj.Placement}
    {mem : Memory} (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hL : (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded mem) :
    (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded
      (ProofLib.stripExecOutside keepR mem) := by
  refine codeLoaded_stripExecOutside_of_keep (fun off hoff => ?_) hL
  have hbase : (pureWordsProg pl.base (fromUtf8PatchedWords pl)).base = pl.base := rfl
  have hlen : (pureWordsProg pl.base (fromUtf8PatchedWords pl)).code.length = 624 := by
    rw [pureWordsProg_code_length, fromUtf8PatchedWords_length]
  rw [hbase]
  exact hcov off (hlen ▸ hoff)

/-- Entry-state `lr` guard at `s0` for `from_utf8` stub replay
    (`keepFromUtf8Block entryTarget lr = false ∧ lr ≠ stubPc`). -/
@[expose] def FromUtf8EntryGuard (entryTarget stubPc : BitVec 64) (s0 : State) : Prop :=
  keepFromUtf8Block entryTarget (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem fromUtf8EntryGuard_iff_trapEntryGuard (pl : Obj.Placement) (stubPc : BitVec 64)
    (s0 : State) :
    FromUtf8EntryGuard pl.base stubPc s0 ↔ TrapEntryGuard (fromUtf8Region pl) stubPc s0 := by
  simp only [FromUtf8EntryGuard, TrapEntryGuard, keepOf_fromUtf8Region_apply]

/-! ## 2. `TrapHook` Instances (Idealized CLI `fromUtf8Hook`, Fallback, `linkedCallHookG`, & Ghost) -/

/-- `keepFsTrace` preserves `.status`, `.pc`, and `.regs` (`readReg64 .lr`), so it preserves
    `TrapHook L` for any `f : State → State`. -/
theorem trapHook_keepFsTrace {L : BitVec 64} {f : State → State}
    (hf : TrapHook L f) :
    TrapHook L (keepFsTrace f) :=
  hf

/-- Current CLI `fromUtf8Hook err` (`CliRun.lean:476`) either raises `.Exception` via `unmodelled`
    or returns via `retHook (fun s => s.setMem ...)` with `status = .Running`, `pc = lr`, and `lr`
    unchanged, so it satisfies `TrapHook L` for every `err` and every `L : BitVec 64`. -/
theorem trapHook_fromUtf8Hook
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) (L : BitVec 64) :
    TrapHook L (fromUtf8Hook err) := by
  classical
  intro w hrun hlr
  unfold fromUtf8Hook
  dsimp only
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨hrun, hlr, hlr⟩
  · exact Or.inr ⟨hrun, hlr, hlr⟩

theorem trapHook_keepFsTrace_fromUtf8Hook
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) (L : BitVec 64) :
    TrapHook L (keepFsTrace (fromUtf8Hook err)) :=
  trapHook_keepFsTrace (trapHook_fromUtf8Hook err L)

theorem trapHook_defaultFromUtf8Hook (L : BitVec 64) :
    TrapHook L defaultFromUtf8Hook :=
  trapHook_fromUtf8Hook _ L

theorem trapHook_keepFsTrace_defaultFromUtf8Hook (L : BitVec 64) :
    TrapHook L (keepFsTrace defaultFromUtf8Hook) :=
  trapHook_keepFsTrace_fromUtf8Hook _ L

/-- `W`-independent `realFromUtf8Fallback` (`retHook realFromUtf8Body`, modifying only `.mem` and
    `.pc := lr`) satisfies `TrapHook L` for every `L : BitVec 64`. -/
theorem trapHook_realFromUtf8Fallback (L : BitVec 64) :
    TrapHook L realFromUtf8Fallback :=
  fun _ hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem trapHook_keepFsTrace_realFromUtf8Fallback (L : BitVec 64) :
    TrapHook L (keepFsTrace realFromUtf8Fallback) :=
  trapHook_keepFsTrace (trapHook_realFromUtf8Fallback L)

/-- Generic state-guarded `linkedCallHookG` combinator: whenever `keep L = true` and
    `TrapHook L (keepFsTrace fallback)` holds, `linkedCallHookG` satisfies `TrapHook L` regardless
    of `Guard`. -/
theorem trapHook_linkedCallHookG {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State} {L : BitVec 64}
    (hkeepL : keep L = true) (hfb : TrapHook L (keepFsTrace fallback)) :
    TrapHook L (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w hrun hlr
  rw [linkedCallHookG_of_keepLr_true (hlr ▸ hkeepL)]
  by_cases hAct : ActiveRealPre spec w
  · simp only [hAct, ↓reduceDIte]
    exact hfb w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    simp [hAct]

/-- Plain guarded `fromUtf8GhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_fromUtf8GhostHook
    (tbl : BitVec 64) {keepR : BitVec 64 → Bool} (P_real P_sub : Program)
    (entryTarget : BitVec 64) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (fromUtf8GhostHook tbl keepR P_real P_sub entryTarget) :=
  trapHook_linkedCallHookG hkeepL (trapHook_keepFsTrace_realFromUtf8Fallback L)

theorem trapHook_fromUtf8GhostHook_of_cover
    (tbl : BitVec 64) {keepR : BitVec 64 → Bool} (P_real P_sub : Program)
    (entryTarget : BitVec 64) {L : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR entryTarget)
    (hL : keepFromUtf8Block entryTarget L = true) :
    TrapHook L (fromUtf8GhostHook tbl keepR P_real P_sub entryTarget) :=
  trapHook_fromUtf8GhostHook tbl P_real P_sub entryTarget (keep_of_keepCoversFromUtf8 hcov hL)

theorem trapHook_fromUtf8GhostHookPure
    {keepR : BitVec 64 → Bool} (P_real : Program) (pl : Obj.Placement) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (fromUtf8GhostHookPure keepR P_real pl) :=
  trapHook_fromUtf8GhostHook _ P_real _ pl.base hkeepL

theorem trapHook_fromUtf8GhostHookPure_of_cover
    {keepR : BitVec 64 → Bool} (P_real : Program) (pl : Obj.Placement) {L : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hL : keepFromUtf8Block pl.base L = true) :
    TrapHook L (fromUtf8GhostHookPure keepR P_real pl) :=
  trapHook_fromUtf8GhostHook_of_cover _ P_real _ pl.base hcov hL

/-- Plain `W`-independent `emptyFromUtf8GhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_emptyFromUtf8GhostHook
    {keepR : BitVec 64 → Bool} (pl : Obj.Placement) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (emptyFromUtf8GhostHook keepR pl) :=
  trapHook_fromUtf8GhostHookPure _ pl hkeepL

theorem trapHook_emptyFromUtf8GhostHook_of_cover
    {keepR : BitVec 64 → Bool} (pl : Obj.Placement) {L : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hL : keepFromUtf8Block pl.base L = true) :
    TrapHook L (emptyFromUtf8GhostHook keepR pl) :=
  trapHook_fromUtf8GhostHookPure_of_cover _ pl hcov hL

/-- `K`-narrowed guarded `fromUtf8GhostHookK` transitions to `.Exception` whenever `keepR L = true`,
    so it satisfies `TrapHook L`. -/
theorem trapHook_fromUtf8GhostHookK
    (tbl : BitVec 64) {keepR : BitVec 64 → Bool} (P_real P_sub : Program)
    (entryTarget : BitVec 64) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (fromUtf8GhostHookK tbl keepR P_real P_sub entryTarget) :=
  trapHook_of_exception_on_keepLr fun w _ hlr =>
    ⟨"ghost-hook precondition violated",
      by rw [fromUtf8GhostHookK_of_keepLr_true (hlr ▸ hkeepL)]⟩

theorem trapHook_fromUtf8GhostHookK_of_cover
    (tbl : BitVec 64) {keepR : BitVec 64 → Bool} (P_real P_sub : Program)
    (entryTarget : BitVec 64) {L : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR entryTarget)
    (hL : keepFromUtf8Block entryTarget L = true) :
    TrapHook L (fromUtf8GhostHookK tbl keepR P_real P_sub entryTarget) :=
  trapHook_fromUtf8GhostHookK tbl P_real P_sub entryTarget (keep_of_keepCoversFromUtf8 hcov hL)

theorem trapHook_fromUtf8GhostHookPureK
    {keepR : BitVec 64 → Bool} (P_real : Program) (pl : Obj.Placement) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (fromUtf8GhostHookPureK keepR P_real pl) :=
  trapHook_fromUtf8GhostHookK _ P_real _ pl.base hkeepL

theorem trapHook_fromUtf8GhostHookPureK_of_cover
    {keepR : BitVec 64 → Bool} (P_real : Program) (pl : Obj.Placement) {L : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hL : keepFromUtf8Block pl.base L = true) :
    TrapHook L (fromUtf8GhostHookPureK keepR P_real pl) :=
  trapHook_fromUtf8GhostHookK_of_cover _ P_real _ pl.base hcov hL

/-- `K`-narrowed `W`-independent `emptyFromUtf8GhostHookK` satisfies `TrapHook L` whenever
    `keepR L = true`. -/
theorem trapHook_emptyFromUtf8GhostHookK
    {keepR : BitVec 64 → Bool} (pl : Obj.Placement) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (emptyFromUtf8GhostHookK keepR pl) :=
  trapHook_fromUtf8GhostHookPureK _ pl hkeepL

theorem trapHook_emptyFromUtf8GhostHookK_of_cover
    {keepR : BitVec 64 → Bool} (pl : Obj.Placement) {L : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hL : keepFromUtf8Block pl.base L = true) :
    TrapHook L (emptyFromUtf8GhostHookK keepR pl) :=
  trapHook_fromUtf8GhostHookPureK_of_cover _ pl hcov hL

/-! ## 3. Entry-Excluded Region Extern Adapters (`REV-S2 F1`) -/

/-- Fixed-`L` entry-excluded extern adapter (`entries = [pl.base]`): on the ghost route `pl.base`
    is hooked inside `keepFromUtf8Block pl.base`, while every `pc ≠ pl.base` in the block has
    `P_ghost.externAt? pc = none` (`REV-S2 F1`, matching STARTUP C2's
    `f3Row_ghostProg617_externAt_none_of_ne_entry`). -/
theorem fromUtf8_reg_ext_of_entry_excluded {P_ghost : Program} {pl : Obj.Placement} {L : BitVec 64}
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hentry : P_ghost.externAt? pl.base = none ∨
      ∃ f, P_ghost.externAt? pl.base = some f ∧ TrapHook L f) :
    ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f := by
  intro pc hkp
  have h := reg_ext_of_entry_excluded (P_ghost := P_ghost) (region := fromUtf8Region pl)
    (entries := [pl.base]) (L := L)
    (fun q hq hmem =>
      hno_ext_outside q (keepOf_fromUtf8Region_apply pl q ▸ hq)
        (fun heq => hmem (List.mem_singleton.mpr heq)))
    (fun e he => by rw [List.mem_singleton] at he; subst he; exact hentry)
    pc ((keepOf_fromUtf8Region_apply pl pc).symm ▸ hkp)
  exact h

/-- `∀ L` entry-excluded extern adapter (`entries = [pl.base]`): bridges STARTUP C2's
    entry-excluded `externAt? pc = none` (`pc ≠ pl.base`) plus a uniform `TrapHook` witness at
    `pl.base` directly into the post-hook and at-stub corollaries (`REV-S2 F1`). -/
theorem fromUtf8_reg_ext_forall_of_entry_excluded {P_ghost : Program} {pl : Obj.Placement}
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hentry : P_ghost.externAt? pl.base = none ∨
      ∃ f, P_ghost.externAt? pl.base = some f ∧
        ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f) :
    ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f := by
  intro pc hkp
  have h := reg_ext_forall_of_entry_excluded (P_ghost := P_ghost) (region := fromUtf8Region pl)
    (entries := [pl.base])
    (fun q hq hmem =>
      hno_ext_outside q (keepOf_fromUtf8Region_apply pl q ▸ hq)
        (fun heq => hmem (List.mem_singleton.mpr heq)))
    (fun e he => by
      rw [List.mem_singleton] at he; subst he
      exact hentry.imp id fun ⟨f, hf, htf⟩ =>
        ⟨f, hf, fun L hL => htf L (keepOf_fromUtf8Region_apply pl L ▸ hL)⟩)
    pc ((keepOf_fromUtf8Region_apply pl pc).symm ▸ hkp)
  exact h.imp id fun ⟨f, hf, htf⟩ =>
    ⟨f, hf, fun L hL => htf L ((keepOf_fromUtf8Region_apply pl L).symm ▸ hL)⟩

/-! ## 4. Post-Hook (`REV-S2 H1`), At-Call, At-Stub, & Ready-to-Apply Ghost Corollaries -/

/-- **Post-hook continuation `keepFromUtf8Block pl.base (u.readReg64 .lr) = false` (`REV-S2 H1`):**
    Consumes `hCode_fu : P_sub.CodeLoaded (f_u u).mem` and `hrest : Steps P_ghost (f_u u) sf`
    directly (`GhostRowReplayOn.replay_at_stub` Arm 2 does not give `P_sub.CodeLoaded s0.mem`;
    card `c` derives `hCode_fu` from `InvS u` + `u.mem.KeepsFrozen (f_u u).mem`). -/
theorem fromUtf8_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (htrap_u : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepFromUtf8Block pl.base sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  rw [← keepOf_fromUtf8Region_apply pl]
  exact lr_trap_after_hook_ret
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_fromUtf8Region_apply pl _ ▸ hL) pc
        (keepOf_fromUtf8Region_apply pl _ ▸ hkp))
    (fromUtf8Region_codeLoaded_iff.mpr hCode_fu)
    hrest hrun_u
    (fun hr => (keepOf_fromUtf8Region_apply pl _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

/-- Post-hook `Returned`-case `keepFromUtf8Block pl.base (u.readReg64 .lr) = false` (`REV-S2 H1`:
    takes `P_sub.CodeLoaded (f_u u).mem` directly). -/
theorem fromUtf8_lr_trap_after_hook_returned
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_u : State → State} {s0 u sf : State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (htrap_u : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false) :
    keepFromUtf8Block pl.base (u.readReg64 .lr) = false :=
  fromUtf8_lr_trap_after_hook_ret hHas htrap_u hreg_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- **`REV-S2 H1` post-hook outcome theorem (`P_sub.CodeLoaded (f_stub u).mem` variant):**
    `GhostRowReplayOn.replay_at_stub` does not provide `P_sub.CodeLoaded s0.mem`; card `c` passes
    `P_sub.CodeLoaded (f_stub u).mem` obtained from `InvS u` + `u.mem.KeepsFrozen (f_stub u).mem`. -/
theorem fromUtf8_keepLr_false_after_hook_of_outcome_post
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_stub : State → State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreg_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      P_sub.CodeLoaded (f_stub u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  intro u hsteps_fu_sf hrun_u hCode_fu
  exact fromUtf8_lr_trap_after_hook_ret hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    hCode_fu hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

/-- Direct `SubroutineOutcome` wrapper for `fromUtf8_keepLr_false_after_hook_of_outcome_post`
    (`REV-S2 H1`: consumes `P_sub.CodeLoaded (f_stub u).mem` directly). -/
theorem fromUtf8_keepLr_false_after_hook_of_subroutineOutcome_post
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_stub : State → State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreg_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      P_sub.CodeLoaded (f_stub u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact fromUtf8_keepLr_false_after_hook_of_outcome_post hHas hreg_ext htrap_stub
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Trajectory `s0.mem` post-hook outcome theorem (1:1 parity with `BcmpLrTrap`; note `REV-S2 H1`:
    `GhostRowReplayOn.replay_at_stub` does not give `P_sub.CodeLoaded s0.mem`, so card `c` uses
    `fromUtf8_keepLr_false_after_hook_of_outcome_post` with `P_sub.CodeLoaded (f_stub u).mem` from
    `InvS u` + `KeepsFrozen`). -/
theorem fromUtf8_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_stub : State → State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreg_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_fu_sf hrun_u hkf
  rw [← keepOf_fromUtf8Region_apply pl]
  exact keepLr_false_after_hook_of_outcome
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_fromUtf8Region_apply pl _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_fromUtf8Region_apply pl _ ▸ hL)⟩)
    (fun L hL => htrap_stub L (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fromUtf8Region_codeLoaded_iff.mpr hc_codeLoaded)
    ((keepOf_fromUtf8Region_apply pl _).trans hlr_s0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_fu_sf hrun_u hkf

/-- Direct `SubroutineOutcome` wrapper for `fromUtf8_keepLr_false_after_hook_of_outcome` (see
    `fromUtf8_keepLr_false_after_hook_of_subroutineOutcome_post` for the `REV-S2 H1`
    `P_sub.CodeLoaded (f_stub u).mem` form). -/
theorem fromUtf8_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_stub : State → State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreg_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  intro u h1 h2 h3 h4
  rw [← keepOf_fromUtf8Region_apply pl]
  exact keepLr_false_after_hook_of_subroutineOutcome
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_fromUtf8Region_apply pl _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_fromUtf8Region_apply pl _ ▸ hL)⟩)
    (fun L hL => htrap_stub L (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fromUtf8Region_codeLoaded_iff.mpr hc_codeLoaded)
    ((keepOf_fromUtf8Region_apply pl _).trans hlr_s0)
    hout u h1 h2 h3 h4

/-- Call-point `keepFromUtf8Block pl.base (u.readReg64 .lr) = false` on `Steps P_ghost u sf`
    covering both non-`.Running` and `Returned` outcomes. -/
theorem fromUtf8_lr_trap_at_call_ret
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (htrap_u : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepFromUtf8Block pl.base sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  rw [← keepOf_fromUtf8Region_apply pl]
  exact lr_trap_at_call_ret
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_fromUtf8Region_apply pl _ ▸ hL) pc
        (keepOf_fromUtf8Region_apply pl _ ▸ hkp))
    hext_u
    (fromUtf8Region_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hu_ne_sf
    (fun hr => (keepOf_fromUtf8Region_apply pl _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

/-- Non-`.Running` terminal call-point `keepFromUtf8Block pl.base (u.readReg64 .lr) = false`. -/
theorem fromUtf8_lr_trap_at_call
    {P_ghost P_sub : Program} {pl : Obj.Placement} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (htrap_u : keepFromUtf8Block pl.base (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hno_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_u)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  rw [← keepOf_fromUtf8Region_apply pl]
  exact lr_trap_at_call
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fun pc hkp => hno_ext pc (keepOf_fromUtf8Region_apply pl _ ▸ hkp))
    hext_u
    (fromUtf8Region_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

/-- At-stub trajectory `keepFromUtf8Block pl.base (u.readReg64 .lr) = false` from outcome facts. -/
theorem fromUtf8_keepLr_false_at_stub_of_outcome
    {P_ghost P_sub : Program} {pl : Obj.Placement} {stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreg_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : FromUtf8EntryGuard pl.base stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  rw [← keepOf_fromUtf8Region_apply pl]
  exact keepLr_false_at_stub_of_outcome
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_fromUtf8Region_apply pl _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_fromUtf8Region_apply pl _ ▸ hL)⟩)
    hext_stub
    (fun L hL => htrap_stub L (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fromUtf8Region_codeLoaded_iff.mpr hc_codeLoaded)
    ((fromUtf8EntryGuard_iff_trapEntryGuard pl stubPc s0).mp hGuard0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_u_sf hrun_u hpc_u

/-- At-stub `SubroutineOutcome` theorem `keepFromUtf8Block pl.base (u.readReg64 .lr) = false`. -/
theorem fromUtf8_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {pl : Obj.Placement} {stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords pl.base (fromUtf8PatchedWords pl))
    (hreg_ext : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : FromUtf8EntryGuard pl.base stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  intro u h1 h2 h3 h4
  rw [← keepOf_fromUtf8Region_apply pl]
  exact keepLr_false_at_stub_of_subroutineOutcome
    (fromUtf8_regionWordsSafe pl)
    (fromUtf8Region_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_fromUtf8Region_apply pl _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_fromUtf8Region_apply pl _ ▸ hL)⟩)
    hext_stub
    (fun L hL => htrap_stub L (keepOf_fromUtf8Region_apply pl _ ▸ hL))
    (fromUtf8Region_codeLoaded_iff.mpr hc_codeLoaded)
    ((fromUtf8EntryGuard_iff_trapEntryGuard pl stubPc s0).mp hGuard0)
    hout u h1 h2 h3 h4

/-- Ready-to-apply entry-excluded (`REV-S2 F1`) + post-hook `CodeLoaded` (`REV-S2 H1`) card-`c`
    outcome corollary for `emptyFromUtf8GhostHook` over `pureWordsProg pl.base (fromUtf8PatchedWords pl)`. -/
theorem emptyFromUtf8GhostHook_keepLr_false_after_hook_of_outcome_post
    {P_ghost : Program} {keepR : BitVec 64 → Bool} {pl : Obj.Placement}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? pl.base = none ∨
      P_ghost.externAt? pl.base = some (emptyFromUtf8GhostHook keepR pl))
    {s0 sf : State}
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost (emptyFromUtf8GhostHook keepR pl u) sf →
      u.status = .Running →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded
        (emptyFromUtf8GhostHook keepR pl u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false :=
  fromUtf8_keepLr_false_after_hook_of_outcome_post
    (pureWordsProg_fromUtf8_hasWords pl)
    (fromUtf8_reg_ext_forall_of_entry_excluded hno_ext_outside
      (hext_entry.imp id fun hs =>
        ⟨_, hs, fun _ hL => trapHook_emptyFromUtf8GhostHook_of_cover pl hcov hL⟩))
    (fun _ hL => trapHook_emptyFromUtf8GhostHook_of_cover pl hcov hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Ready-to-apply entry-excluded (`REV-S2 F1`) + post-hook `CodeLoaded` (`REV-S2 H1`) card-`c`
    `SubroutineOutcome` corollary for `emptyFromUtf8GhostHook`. -/
theorem emptyFromUtf8GhostHook_keepLr_false_after_hook_of_subroutineOutcome_post
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {keepR : BitVec 64 → Bool} {pl : Obj.Placement}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? pl.base = none ∨
      P_ghost.externAt? pl.base = some (emptyFromUtf8GhostHook keepR pl))
    {s0 sf : State}
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost (emptyFromUtf8GhostHook keepR pl u) sf →
      u.status = .Running →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded
        (emptyFromUtf8GhostHook keepR pl u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact emptyFromUtf8GhostHook_keepLr_false_after_hook_of_outcome_post hcov hno_ext_outside
    hext_entry hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Ready-to-apply entry-excluded (`REV-S2 F1`) card-`c` at-stub `SubroutineOutcome` corollary for
    `emptyFromUtf8GhostHook`. -/
theorem emptyFromUtf8GhostHook_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {keepR : BitVec 64 → Bool} {pl : Obj.Placement} {stubPc : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? pl.base = none ∨
      P_ghost.externAt? pl.base = some (emptyFromUtf8GhostHook keepR pl))
    (hext_stub : P_ghost.externAt? stubPc = some (emptyFromUtf8GhostHook keepR pl))
    {s0 sf : State}
    (hc_codeLoaded : (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded s0.mem)
    (hGuard0 : FromUtf8EntryGuard pl.base stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false :=
  fromUtf8_keepLr_false_at_stub_of_subroutineOutcome
    (pureWordsProg_fromUtf8_hasWords pl)
    (fromUtf8_reg_ext_forall_of_entry_excluded hno_ext_outside
      (hext_entry.imp id fun hs =>
        ⟨_, hs, fun _ hL => trapHook_emptyFromUtf8GhostHook_of_cover pl hcov hL⟩))
    hext_stub
    (fun _ hL => trapHook_emptyFromUtf8GhostHook_of_cover pl hcov hL)
    hc_codeLoaded hGuard0 hout

/-- Ready-to-apply entry-excluded (`REV-S2 F1`) + post-hook `CodeLoaded` (`REV-S2 H1`) card-`c`
    outcome corollary for `K`-narrowed `emptyFromUtf8GhostHookK`. -/
theorem emptyFromUtf8GhostHookK_keepLr_false_after_hook_of_outcome_post
    {P_ghost : Program} {keepR : BitVec 64 → Bool} {pl : Obj.Placement}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? pl.base = none ∨
      P_ghost.externAt? pl.base = some (emptyFromUtf8GhostHookK keepR pl))
    {s0 sf : State}
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost (emptyFromUtf8GhostHookK keepR pl u) sf →
      u.status = .Running →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded
        (emptyFromUtf8GhostHookK keepR pl u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false :=
  fromUtf8_keepLr_false_after_hook_of_outcome_post
    (pureWordsProg_fromUtf8_hasWords pl)
    (fromUtf8_reg_ext_forall_of_entry_excluded hno_ext_outside
      (hext_entry.imp id fun hs =>
        ⟨_, hs, fun _ hL => trapHook_emptyFromUtf8GhostHookK_of_cover pl hcov hL⟩))
    (fun _ hL => trapHook_emptyFromUtf8GhostHookK_of_cover pl hcov hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Ready-to-apply entry-excluded (`REV-S2 F1`) + post-hook `CodeLoaded` (`REV-S2 H1`) card-`c`
    `SubroutineOutcome` corollary for `K`-narrowed `emptyFromUtf8GhostHookK`. -/
theorem emptyFromUtf8GhostHookK_keepLr_false_after_hook_of_subroutineOutcome_post
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {keepR : BitVec 64 → Bool} {pl : Obj.Placement}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? pl.base = none ∨
      P_ghost.externAt? pl.base = some (emptyFromUtf8GhostHookK keepR pl))
    {s0 sf : State}
    (hlr_s0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost (emptyFromUtf8GhostHookK keepR pl u) sf →
      u.status = .Running →
      (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded
        (emptyFromUtf8GhostHookK keepR pl u).mem →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact emptyFromUtf8GhostHookK_keepLr_false_after_hook_of_outcome_post hcov hno_ext_outside
    hext_entry hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Ready-to-apply entry-excluded (`REV-S2 F1`) card-`c` at-stub `SubroutineOutcome` corollary for
    `K`-narrowed `emptyFromUtf8GhostHookK`. -/
theorem emptyFromUtf8GhostHookK_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {keepR : BitVec 64 → Bool} {pl : Obj.Placement} {stubPc : BitVec 64}
    (hcov : KeepCoversFromUtf8 keepR pl.base)
    (hno_ext_outside : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true → pc ≠ pl.base →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? pl.base = none ∨
      P_ghost.externAt? pl.base = some (emptyFromUtf8GhostHookK keepR pl))
    (hext_stub : P_ghost.externAt? stubPc = some (emptyFromUtf8GhostHookK keepR pl))
    {s0 sf : State}
    (hc_codeLoaded : (pureWordsProg pl.base (fromUtf8PatchedWords pl)).CodeLoaded s0.mem)
    (hGuard0 : FromUtf8EntryGuard pl.base stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepFromUtf8Block pl.base (u.readReg64 .lr) = false :=
  fromUtf8_keepLr_false_at_stub_of_subroutineOutcome
    (pureWordsProg_fromUtf8_hasWords pl)
    (fromUtf8_reg_ext_forall_of_entry_excluded hno_ext_outside
      (hext_entry.imp id fun hs =>
        ⟨_, hs, fun _ hL => trapHook_emptyFromUtf8GhostHookK_of_cover pl hcov hL⟩))
    hext_stub
    (fun _ hL => trapHook_emptyFromUtf8GhostHookK_of_cover pl hcov hL)
    hc_codeLoaded hGuard0 hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap
