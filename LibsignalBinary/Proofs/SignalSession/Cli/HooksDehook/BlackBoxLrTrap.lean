/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import

/-!
# Closed-`lr` Trap & Subroutine-Outcome `keepBlackBox lr = false` Suite (`HooksDehook.BlackBoxLrTrap`)

Row 3 of Card **D-d** (`dd_dalek_lrtrap.md`): proves that inside the 20-byte (`5`-word)
`subtle::black_box::<u8>` block (`blackBoxU8Words`: `sub sp,#16; strb; ldrb; add sp,#16; ret`) at
`entry`, no execution path writes `x30` (`lr`) or leaves `[entry, entry + 20)` except via `ret x30`
to `lr`. Exports:
1. Region & `keepBlackBox` (`blackBoxByteLen = 20`, `blackBoxRegion`, `blackBoxU8_all_safe` by
   `decide`, `blackBox_regionWordsSafe`, `hasWords` / `CodeLoaded` / `BlackBoxEntryGuard`).
2. `TrapHook` instances for `blackBoxHook`, `keepFsTrace blackBoxHook`, plain `blackBoxGhostHook` /
   `f3EmptyBlackBoxGhostHook`, and `K`-narrowed `blackBoxGhostHookK` / `f3EmptyBlackBoxGhostHookK`.
3. Post-hook (`P_sub.CodeLoaded u.mem` at `u` per `H1`, plus `s0.mem` companion) and at-stub
   `SubroutineOutcome` trap corollaries, plus entry-excluded (`pc ≠ entry` / `pc ≠ stubPc`, per `F1`)
   `f3EmptyBlackBoxGhostHook{,K}` wrappers matching STARTUP's
   `f3Row_ghostProg617_externAt_none_of_ne_entry`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open CryptoVerification.LibsignalSession (blackBoxHook)
open LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 (blackBoxU8Words)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  TrapHook trapHook_of_exception_on_keepLr trapHook_linkedCallHook
  lr_trap_at_call_ret lr_trap_at_call TrapEntryGuard keepLr_false_at_stub_of_outcome
  checkWordsTrapSafe regionWordsSafe_single
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (
  lr_trap_after_hook_ret
  keepLr_false_after_hook_of_outcome
  keepLr_false_after_hook_of_subroutineOutcome
  keepLr_false_at_stub_of_subroutineOutcome
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode (
  pureWordsProg_blackBoxU8_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost (
  blackBoxGhostHook blackBoxGhostHookK
  f3EmptyBlackBoxGhostHook f3EmptyBlackBoxGhostHookK
  f3EmptyBlackBoxGhostHook_eq f3EmptyBlackBoxGhostHookK_eq
  keepFsTrace_blackBoxHook_eq blackBoxGhostHookK_of_keepLr_true
)

/-! ## 1. 20 B `black_box::<u8>` Region (`keepBlackBox`, `blackBoxRegion`, `RegionWordsSafe`) -/

/-- Byte length (`20 = 4 * 5`) of `subtle::black_box::<u8>` (`blackBoxU8Words`). -/
@[expose] def blackBoxByteLen : Nat :=
  4 * blackBoxU8Words.length

theorem blackBoxByteLen_eq : blackBoxByteLen = 20 := rfl

theorem blackBoxU8Words_length : blackBoxU8Words.length = 5 := rfl

theorem four_mul_blackBoxU8Words_length :
    4 * blackBoxU8Words.length = blackBoxByteLen := rfl

/-- Kept-region byte predicate `[entry, entry + 20)` for `subtle::black_box::<u8>`. -/
@[expose] def keepBlackBox (entry : BitVec 64) : BitVec 64 → Bool :=
  keepBlock entry blackBoxByteLen

theorem keepBlackBox_iff (entry pc : BitVec 64) :
    keepBlackBox entry pc = true ↔ (pc - entry).toNat < blackBoxByteLen := by
  simp [keepBlackBox, keepBlock, decide_eq_true_eq]

/-- The `black_box::<u8>` entry `entry` lies inside `keepBlackBox entry`. -/
theorem keepBlackBox_entry (entry : BitVec 64) :
    keepBlackBox entry entry = true := by
  rw [keepBlackBox_iff, blackBoxByteLen_eq]
  have hsub : entry - entry = 0#64 := by bv_omega
  rw [hsub]
  decide

/-- Single-block `TrapRegion` for the 5-word `blackBoxU8Words` block at `entry`. -/
@[expose] def blackBoxRegion (entry : BitVec 64) : TrapRegion :=
  [(entry, blackBoxU8Words)]

/-- `keepOf (blackBoxRegion entry)` equals `keepBlackBox entry`. -/
theorem keepOf_blackBoxRegion (entry : BitVec 64) :
    keepOf (blackBoxRegion entry) = keepBlackBox entry := by
  funext pc
  dsimp only [blackBoxRegion]
  rw [keepOf_singleton, four_mul_blackBoxU8Words_length]
  rfl

theorem keepOf_blackBoxRegion_apply (entry pc : BitVec 64) :
    keepOf (blackBoxRegion entry) pc = keepBlackBox entry pc :=
  congrFun (keepOf_blackBoxRegion entry) pc

/-- All 5 words of `blackBoxU8Words` (`sub sp,#16; strb; ldrb; add sp,#16; ret`) pass
    `checkWordsTrapSafe` with `allowed = []`. -/
theorem blackBoxU8_all_safe :
    checkWordsTrapSafe blackBoxU8Words [] = true := by
  decide

/-- `RegionWordsSafe` for `blackBoxRegion entry` at any `entry : BitVec 64`. -/
theorem blackBox_regionWordsSafe (entry : BitVec 64) :
    RegionWordsSafe (blackBoxRegion entry) :=
  regionWordsSafe_single entry blackBoxU8_all_safe

/-- `RegionHasWords [P_sub] (blackBoxRegion entry)` from `P_sub.hasWords entry blackBoxU8Words`. -/
theorem blackBoxRegion_hasWords_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words) :
    RegionHasWords [P_sub] (blackBoxRegion entry) := by
  intro blk hmem
  rw [blackBoxRegion, List.mem_singleton] at hmem
  subst hmem
  exact ⟨P_sub, List.mem_singleton.mpr rfl, hHas⟩

/-- Unconditional `RegionHasWords` for `pureWordsProg entry blackBoxU8Words`. -/
theorem blackBoxRegion_hasWords_pure (entry : BitVec 64) :
    RegionHasWords [pureWordsProg entry blackBoxU8Words] (blackBoxRegion entry) :=
  blackBoxRegion_hasWords_of_hasWords (pureWordsProg_blackBoxU8_hasWords entry)

theorem blackBoxRegion_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem := by
  constructor
  · intro h
    exact h P_sub (List.mem_singleton.mpr rfl)
  · intro h P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact h

theorem blackBox_codeLoaded_stripExecOutside {keep : BitVec 64 → Bool} {P_sub : Program}
    {mem : Memory}
    (hkeep : ∀ off : Nat, off < P_sub.code.length →
      keep (P_sub.base + BitVec.ofNat 64 off) = true)
    (hL : P_sub.CodeLoaded mem) :
    P_sub.CodeLoaded (ProofLib.stripExecOutside keep mem) :=
  codeLoaded_stripExecOutside_of_keep hkeep hL

/-- Entry-state `lr` guard at `s0` for `black_box` stub replay
    (`keepBlackBox entry lr = false ∧ lr ≠ stubPc`). -/
@[expose] def BlackBoxEntryGuard (entry stubPc : BitVec 64) (s0 : State) : Prop :=
  keepBlackBox entry (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem blackBoxEntryGuard_iff_trapEntryGuard (entry stubPc : BitVec 64) (s0 : State) :
    BlackBoxEntryGuard entry stubPc s0 ↔ TrapEntryGuard (blackBoxRegion entry) stubPc s0 := by
  simp only [BlackBoxEntryGuard, TrapEntryGuard, keepOf_blackBoxRegion_apply]

/-! ## 2. `TrapHook` Instances (Stock `blackBoxHook`, Plain Ghost, and `K` Ghost) -/

/-- Stock `blackBoxHook` updates `x0` and returns to `lr` while `.Running` with `lr` unchanged, so
    it satisfies `TrapHook L` for every `L : BitVec 64`. -/
theorem trapHook_blackBoxHook (L : BitVec 64) :
    TrapHook L blackBoxHook := by
  intro w hrun hlr
  unfold blackBoxHook retHook
  exact Or.inr ⟨hrun, hlr, hlr⟩

theorem trapHook_keepFsTrace_blackBoxHook (L : BitVec 64) :
    TrapHook L (keepFsTrace blackBoxHook) := by
  intro w hrun hlr
  rw [keepFsTrace_blackBoxHook_eq]
  exact trapHook_blackBoxHook L w hrun hlr

/-- Plain `blackBoxGhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_blackBoxGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (blackBoxGhostHook keepR P_real P_sub entryTarget) :=
  trapHook_linkedCallHook hkeepL (trapHook_keepFsTrace_blackBoxHook L)

theorem trapHook_blackBoxGhostHook_of_cover {keepR : BitVec 64 → Bool} {entry L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hL : keepBlackBox entry L = true) :
    TrapHook L (blackBoxGhostHook keepR P_real P_sub entryTarget) :=
  trapHook_blackBoxGhostHook P_real P_sub entryTarget (hcover L hL)

/-- Plain `W`-independent `f3EmptyBlackBoxGhostHook` satisfies `TrapHook L` whenever
    `keepR L = true`. -/
theorem trapHook_f3EmptyBlackBoxGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget) := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact trapHook_blackBoxGhostHook _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyBlackBoxGhostHook_of_cover {keepR : BitVec 64 → Bool} {entry L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hL : keepBlackBox entry L = true) :
    TrapHook L (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget) :=
  trapHook_f3EmptyBlackBoxGhostHook P_sub entryTarget (hcover L hL)

/-- `K`-narrowed `blackBoxGhostHookK` transitions to `.Exception` whenever `keepR L = true`, so it
    satisfies `TrapHook L`. -/
theorem trapHook_blackBoxGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (blackBoxGhostHookK keepR P_real P_sub entryTarget) :=
  trapHook_of_exception_on_keepLr fun w _ hlr =>
    ⟨"ghost-hook precondition violated", by rw [blackBoxGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]⟩

theorem trapHook_blackBoxGhostHookK_of_cover {keepR : BitVec 64 → Bool} {entry L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hL : keepBlackBox entry L = true) :
    TrapHook L (blackBoxGhostHookK keepR P_real P_sub entryTarget) :=
  trapHook_blackBoxGhostHookK P_real P_sub entryTarget (hcover L hL)

/-- `K`-narrowed `W`-independent `f3EmptyBlackBoxGhostHookK` satisfies `TrapHook L` whenever
    `keepR L = true`. -/
theorem trapHook_f3EmptyBlackBoxGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget) := by
  rw [f3EmptyBlackBoxGhostHookK_eq]
  exact trapHook_blackBoxGhostHookK _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyBlackBoxGhostHookK_of_cover {keepR : BitVec 64 → Bool} {entry L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hL : keepBlackBox entry L = true) :
    TrapHook L (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget) :=
  trapHook_f3EmptyBlackBoxGhostHookK P_sub entryTarget (hcover L hL)

/-! ## 3. Post-Hook Continuation & At-Stub `SubroutineOutcome` Trap Corollaries for Card `c` -/

/-- Post-hook continuation `keepBlackBox entry (u.readReg64 .lr) = false`. -/
theorem blackBox_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (htrap_u : keepBlackBox entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBlackBox entry (u.readReg64 .lr) = true → ∀ pc, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepBlackBox entry sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepBlackBox entry (u.readReg64 .lr) = false := by
  rw [← keepOf_blackBoxRegion_apply entry]
  exact lr_trap_after_hook_ret
    (blackBox_regionWordsSafe entry)
    (blackBoxRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_blackBoxRegion_apply entry _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_blackBoxRegion_apply entry _ ▸ hL) pc
        (keepOf_blackBoxRegion_apply entry _ ▸ hkp))
    (blackBoxRegion_codeLoaded_iff.mpr hCode_fu)
    hrest hrun_u
    (fun hr => (keepOf_blackBoxRegion_apply entry _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

/-- Post-hook `Returned`-case `keepBlackBox entry (u.readReg64 .lr) = false` when `sf` is
    `.Running` at `sf.pc = s0.readReg64 .lr`. -/
theorem blackBox_lr_trap_after_hook_returned
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {s0 u sf : State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (htrap_u : keepBlackBox entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBlackBox entry (u.readReg64 .lr) = true → ∀ pc, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false) :
    keepBlackBox entry (u.readReg64 .lr) = false :=
  blackBox_lr_trap_after_hook_ret hHas htrap_u hreg_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- **Card-`c` `InvS u` post-hook theorem (`blackBox_keepLr_false_after_hook_of_codeLoaded_u`):**
    Consumes `P_sub.CodeLoaded u.mem` at the call state `u` (supplied by `InvS u` in
    `GhostRowReplayOn.replay_at_stub` Arm 2) + `u.mem.KeepsFrozen (f_stub u).mem`. -/
theorem blackBox_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hreg_ext : ∀ pc : BitVec 64, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  intro u hc_u hsteps_fu_sf hrun_u hkf
  exact blackBox_lr_trap_after_hook_ret hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (hc_u.of_keepsFrozen hkf)
    hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

/-- Direct `SubroutineOutcome` wrapper for `blackBox_keepLr_false_after_hook_of_codeLoaded_u`. -/
theorem blackBox_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hreg_ext : ∀ pc : BitVec 64, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact blackBox_keepLr_false_after_hook_of_codeLoaded_u hHas hreg_ext htrap_stub
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Trajectory post-hook theorem propagating `hc_codeLoaded : P_sub.CodeLoaded s0.mem`.
    Note (`H1`): `GhostRowReplayOn.replay_at_stub` provides `InvS u` (`P_sub.CodeLoaded u.mem`)
    rather than `P_sub.CodeLoaded s0.mem`; prefer `blackBox_keepLr_false_after_hook_of_codeLoaded_u`
    there. -/
theorem blackBox_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hreg_ext : ∀ pc : BitVec 64, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_fu_sf hrun_u hkf
  rw [← keepOf_blackBoxRegion_apply entry]
  exact keepLr_false_after_hook_of_outcome
    (blackBox_regionWordsSafe entry)
    (blackBoxRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_blackBoxRegion_apply entry _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_blackBoxRegion_apply entry _ ▸ hL)⟩)
    (fun L hL => htrap_stub L (keepOf_blackBoxRegion_apply entry _ ▸ hL))
    (blackBoxRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((keepOf_blackBoxRegion_apply entry _).trans hlr_s0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_fu_sf hrun_u hkf

/-- Direct `SubroutineOutcome` wrapper for `blackBox_keepLr_false_after_hook_of_outcome`. -/
theorem blackBox_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hreg_ext : ∀ pc : BitVec 64, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact blackBox_keepLr_false_after_hook_of_outcome hHas hreg_ext htrap_stub
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Call-point `keepBlackBox entry (u.readReg64 .lr) = false` on `Steps P_ghost u sf`. -/
theorem blackBox_lr_trap_at_call_ret
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (htrap_u : keepBlackBox entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBlackBox entry (u.readReg64 .lr) = true → ∀ pc, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepBlackBox entry sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepBlackBox entry (u.readReg64 .lr) = false := by
  rw [← keepOf_blackBoxRegion_apply entry]
  exact lr_trap_at_call_ret
    (blackBox_regionWordsSafe entry)
    (blackBoxRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_blackBoxRegion_apply entry _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_blackBoxRegion_apply entry _ ▸ hL) pc
        (keepOf_blackBoxRegion_apply entry _ ▸ hkp))
    hext_u
    (blackBoxRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hu_ne_sf
    (fun hr => (keepOf_blackBoxRegion_apply entry _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

/-- Non-`.Running` terminal call-point `keepBlackBox entry (u.readReg64 .lr) = false`. -/
theorem blackBox_lr_trap_at_call
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (htrap_u : keepBlackBox entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hno_ext : ∀ pc, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_u)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepBlackBox entry (u.readReg64 .lr) = false := by
  rw [← keepOf_blackBoxRegion_apply entry]
  exact lr_trap_at_call
    (blackBox_regionWordsSafe entry)
    (blackBoxRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_blackBoxRegion_apply entry _ ▸ hL))
    (fun pc hkp => hno_ext pc (keepOf_blackBoxRegion_apply entry _ ▸ hkp))
    hext_u
    (blackBoxRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

/-- **Card-`c` at-stub trajectory theorem (`blackBox_keepLr_false_at_stub_of_outcome`).** -/
theorem blackBox_keepLr_false_at_stub_of_outcome
    {P_ghost P_sub : Program} {entry stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hreg_ext : ∀ pc : BitVec 64, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BlackBoxEntryGuard entry stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  rw [← keepOf_blackBoxRegion_apply entry]
  exact keepLr_false_at_stub_of_outcome
    (blackBox_regionWordsSafe entry)
    (blackBoxRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_blackBoxRegion_apply entry _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_blackBoxRegion_apply entry _ ▸ hL)⟩)
    hext_stub
    (fun L hL => htrap_stub L (keepOf_blackBoxRegion_apply entry _ ▸ hL))
    (blackBoxRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((blackBoxEntryGuard_iff_trapEntryGuard entry stubPc s0).mp hGuard0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_u_sf hrun_u hpc_u

/-- **Card-`c` at-stub `SubroutineOutcome` theorem
    (`blackBox_keepLr_false_at_stub_of_subroutineOutcome`).** -/
theorem blackBox_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {entry stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hreg_ext : ∀ pc : BitVec 64, keepBlackBox entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBlackBox entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BlackBoxEntryGuard entry stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact blackBox_keepLr_false_at_stub_of_outcome hHas hreg_ext hext_stub htrap_stub
    hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-- Parametric `∀ L` adapter bridging entry-excluded `externAt? pc = none` (`pc ∉ entries`) plus
    uniform per-entry `TrapHook` witnesses into the `blackBox_*` theorems. -/
theorem blackBox_reg_ext_of_entry_excluded {P_ghost : Program} {entry : BitVec 64}
    {entries : List (BitVec 64)}
    (hno_ext_outside : ∀ pc, keepBlackBox entry pc = true → pc ∉ entries → P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries, P_ghost.externAt? e = none ∨
      ∃ f, P_ghost.externAt? e = some f ∧ ∀ L, keepBlackBox entry L = true → TrapHook L f) :
    ∀ pc, keepBlackBox entry pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepBlackBox entry L = true → TrapHook L f := by
  intro pc hkp
  by_cases hmem : pc ∈ entries
  · exact hentries pc hmem
  · exact Or.inl (hno_ext_outside pc hkp hmem)

/-- Single-stub specialization of `blackBox_reg_ext_of_entry_excluded` (`entries := [stubPc]`; on
    the stock/C2 route, `stubPc = entry`). -/
theorem blackBox_reg_ext_of_stub_excluded {P_ghost : Program} {entry stubPc : BitVec 64}
    {f_stub : State → State}
    (hno_ext_outside : ∀ pc, keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L, keepBlackBox entry L = true → TrapHook L f_stub) :
    ∀ pc, keepBlackBox entry pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepBlackBox entry L = true → TrapHook L f := by
  refine blackBox_reg_ext_of_entry_excluded (entries := [stubPc])
    (fun pc hkp hmem => hno_ext_outside pc hkp (fun hEq => hmem (List.mem_singleton.mpr hEq))) ?_
  intro e he
  rw [List.mem_singleton.mp he]
  exact Or.inr ⟨f_stub, hext_stub, htrap_stub⟩

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `f3EmptyBlackBoxGhostHook`
    (`entries = [entry]` when `stubPc = entry`; consumes `P_sub.CodeLoaded u.mem` at `u`). -/
theorem f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false :=
  blackBox_keepLr_false_after_hook_of_codeLoaded_u hHas
    (blackBox_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBlackBoxGhostHook_of_cover P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyBlackBoxGhostHook_of_cover P_sub entryTarget hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` `InvS u` post-hook `SubroutineOutcome` theorem for
    `f3EmptyBlackBoxGhostHook`. -/
theorem f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u hHas hcover
    hno_ext_outside hext_stub hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` at-stub `SubroutineOutcome` theorem for `f3EmptyBlackBoxGhostHook`. -/
theorem f3EmptyBlackBoxGhostHook_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBlackBoxGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BlackBoxEntryGuard entry stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBlackBox entry (u.readReg64 .lr) = false :=
  blackBox_keepLr_false_at_stub_of_subroutineOutcome hHas
    (blackBox_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBlackBoxGhostHook_of_cover P_sub entryTarget hcover hL))
    hext_stub
    (fun _ hL => trapHook_f3EmptyBlackBoxGhostHook_of_cover P_sub entryTarget hcover hL)
    hc_codeLoaded hGuard0 hout

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `K`-narrowed `f3EmptyBlackBoxGhostHookK`
    (`entries = [entry]` when `stubPc = entry`; consumes `P_sub.CodeLoaded u.mem` at `u`). -/
theorem f3EmptyBlackBoxGhostHookK_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false :=
  blackBox_keepLr_false_after_hook_of_codeLoaded_u hHas
    (blackBox_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBlackBoxGhostHookK_of_cover P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyBlackBoxGhostHookK_of_cover P_sub entryTarget hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` `InvS u` post-hook `SubroutineOutcome` theorem for
    `f3EmptyBlackBoxGhostHookK`. -/
theorem f3EmptyBlackBoxGhostHookK_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepBlackBox entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget u).mem →
      keepBlackBox entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyBlackBoxGhostHookK_keepLr_false_after_hook_of_codeLoaded_u hHas hcover
    hno_ext_outside hext_stub hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` at-stub `SubroutineOutcome` theorem for `f3EmptyBlackBoxGhostHookK`. -/
theorem f3EmptyBlackBoxGhostHookK_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry blackBoxU8Words)
    (hcover : ∀ pc, keepBlackBox entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBlackBox entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBlackBoxGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BlackBoxEntryGuard entry stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBlackBox entry (u.readReg64 .lr) = false :=
  blackBox_keepLr_false_at_stub_of_subroutineOutcome hHas
    (blackBox_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBlackBoxGhostHookK_of_cover P_sub entryTarget hcover hL))
    hext_stub
    (fun _ hL => trapHook_f3EmptyBlackBoxGhostHookK_of_cover P_sub entryTarget hcover hL)
    hc_codeLoaded hGuard0 hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap
