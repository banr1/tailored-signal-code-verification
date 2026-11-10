/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase -- proof-setup: allow-public-import
import ProofLib.BV.Bits

/-!
# Closed-`lr` Trap & Subroutine-Outcome `keepBPreHull lr = false` Suite (`HooksDehook.MemmoveLrTrap`)

Card **L3-d** top-level closed-trap, post-hook / at-stub (`H1`), and Stage A `GhostExternReplaysOn`
corollaries over the `956`-byte (`239`-word) C2 `2C` `.text.b_pre` hull `keepBPreHull m`
(re-exporting `HooksDehook.MemmoveLrTrapBase` via `public import`).

## Review Guardrails (`C4 / H-REV2`, `F1`, `H1`, Pad Halt, `Lib2LayoutFacts` `@ a230f2671b`)

- **Whole-hull trap + pad halt (`[m + 396, m + 400)`):** `bPreHull_trap_impossible` splits
  `keepBPreHull m pc = true` via `MemmoveLrTrapBase.keepBPreHull_cases` into the 3-block
  `bPreCodeRegion` (`fetchMem_trapSafe` + `execInst_of_instrSafeInRegion`) and the 4-byte `0#32`
  pad (`MemmoveLrTrapBase.bPrePad_fetchMem_none`, `P_ghost.fetchMem s1.mem s1.pc = none`, using only
  `Arm64.Step.{exec, halt_unmapped, extern, extern_fault}`).
- **3-Entry `C4` + `F1` stub-exclusion set (`entries := ["memmove", "memcpy", "memset"].map resolve`):**
  Never assumes whole-hull `externAt? = none`. Premise shapes copy verbatim
  `LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfF3Relink/Lib2LayoutFacts.lean` @ `a230f2671b`
  (`origin/stock-lld/c2-startup-dnm`, **NOT imported**): `:392-402`
  `f3RowSyms_ghostProg617_externAt_none_of_ne_entries` (backed by `:346-353`
  `f3RxSeg_ghostProg617_externAt_none_of_ne_entries`, cf. `:316` `C2ExternTableFacts`, `:368`
  `f3Row_ghostProg617_externAt_none_of_ne_entry`, `:114` `keepTextBPre_sub_rxProg`), `:355-362`
  `f3RxSeg_ghostProg617_externAt_entry`, `:485` `f3BatchLEntryGuard_of_startupLr`, `:203`
  `f3CodeInv_rxWords_codeLoaded_strip` (`hAlign : addr.toNat % 4 = 0`), `:428` `StepsVisitedIn`,
  and `:444` `f3RxSeg_steps_realW_of_visitedIn`. Cross-block `"memcpy"` / `"memset"` entries use the
  universal-`L` (`∀ L, TrapHook L f`) witnesses from `MemmoveLrTrapBase` §2 (`MemmoveCode.lean:1155`).
- **Strict `H1`:** Every post-hook and at-stub theorem takes `CodeLoaded` at `(f u).mem` or `u.mem`
  (zero `s0.mem` forms).
- **Stage A replay forms only:** `f3EmptyMemmoveGhostHook_replaysOn_of_{outcome,subroutineOutcome}`
  and `f3PureMemmoveGhostHook_replaysOn_of_subroutineOutcome` target Stage A's
  `Ghost617Transfer.GhostExternReplaysOn` (`MemmoveGhostReplays`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrap

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen ActiveRealPre linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  StubReachesTargetOn GhostExternReplaysOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  execInst_of_instrSafeInRegion fetchMem_trapSafe TrapHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (
  masterMemmoveSpec bPrePadWord bPreMemmoveByteOff
  bPreHullWords pureWordsProg_bPreHull_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (
  keepBPreHull memmoveGhostFn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK (
  f3EmptyMemmoveGhostHook f3EmptyMemmoveGhostHookK
  f3PureMemmoveGhostHook
  f3EmptyMemmoveGhostHook_eq f3EmptyMemmoveGhostHook_master_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays (
  f3EmptyMemmoveGhostHook_replaysOn_of_lrOut
  f3PureMemmoveGhostHook_replaysOn_of_lrOut
  bPreHull3_reg_ext_of_entries
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase (
  KeepCoversBPreHull MemmoveEntryGuard
  bPreCodeRegion_wordsSafe keepBPreHull_of_bPreCodeRegion keepBPreHull_cases
  bPreCodeRegion_hasWords_of_bPreHull bPreCodeRegion_codeLoaded_iff
  codeLoaded_of_stripExecOutside bPrePad_fetchMem_none
  trapHook_f3EmptyMemmoveGhostHook trapHook_f3EmptyMemmoveGhostHook_of_cover
  trapHook_f3EmptyMemmoveGhostHookK_of_cover
)

/-! ## 3. 3-Entry `C4` + `F1` Extern Adapters (`entries := ["memmove", "memcpy", "memset"].map resolve`) -/

/-- Fixed-`L` 3-entry extern adapter on `keepBPreHull m` (`entries := ["memmove", "memcpy",
    "memset"].map resolve`), copying verbatim the premise shapes of
    `Lib2LayoutFacts.lean` @ `a230f2671b` (`origin/stock-lld/c2-startup-dnm`, **NOT imported**):
    - `hOffEntries`: `Lib2LayoutFacts.lean:392-402`
      `f3RowSyms_ghostProg617_externAt_none_of_ne_entries` (backed by `:346-353`
      `f3RxSeg_ghostProg617_externAt_none_of_ne_entries`);
    - `hEntry`: `Lib2LayoutFacts.lean:355-362` `f3RxSeg_ghostProg617_externAt_entry`. -/
theorem bPreHull_reg_ext_of_entries
    {m L : BitVec 64} {P_ghost : Program}
    {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hOffEntries : ∀ {pc : BitVec 64},
      keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve →
      P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveTrap : ∀ f, extOf "memmove" = some f → TrapHook L f)
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → TrapHook L f) :
    ∀ pc : BitVec 64, keepBPreHull m pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f := by
  intro pc hpc
  by_cases hmem : pc ∈ ["memmove", "memcpy", "memset"].map resolve
  · obtain ⟨sym, hsym, rfl⟩ := List.mem_map.mp hmem
    rw [hEntry hsym]
    rcases List.mem_cons.mp hsym with rfl | h1
    · cases he : extOf "memmove" with
      | none => exact Or.inl rfl
      | some f => exact Or.inr ⟨f, rfl, hMemmoveTrap f he⟩
    · rcases List.mem_cons.mp h1 with rfl | h2
      · cases he : extOf "memcpy" with
        | none => exact Or.inl rfl
        | some f => exact Or.inr ⟨f, rfl, hMemcpyTrap f he⟩
      · rcases List.mem_cons.mp h2 with rfl | hnil
        · cases he : extOf "memset" with
          | none => exact Or.inl rfl
          | some f => exact Or.inr ⟨f, rfl, hMemsetTrap f he⟩
        · cases hnil
  · exact Or.inl (hOffEntries hpc hmem)

/-- `∀ L` 3-entry extern adapter on `keepBPreHull m` (`entries := ["memmove", "memcpy",
    "memset"].map resolve`), directly matching `MemmoveGhostReplays.bPreHull3_reg_ext_of_entries`
    (`TrapRetHook = TrapHook` by `rfl`) and citing `Lib2LayoutFacts.lean:392-402, :346-353,
    :355-362` @ `a230f2671b` (**NOT imported**). -/
theorem bPreHull_reg_ext_forall_of_entries
    {m : BitVec 64} {P_ghost : Program}
    {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hOffEntries : ∀ {pc : BitVec 64},
      keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve →
      P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveTrap : ∀ f, extOf "memmove" = some f →
      ∀ L, keepBPreHull m L = true → TrapHook L f)
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f) :
    ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f :=
  bPreHull3_reg_ext_of_entries hOffEntries hEntry hMemmoveTrap hMemcpyTrap hMemsetTrap


/-! ## 4. Whole-Hull `bPreHull_trap_impossible`, Post-Hook / At-Stub (`H1`), & Stage A Replays -/

/-- Closed-trap invariant on the contiguous 956 B `.text.b_pre` hull `keepBPreHull m` with pinned
    `lr = L` and `P_sub.CodeLoaded w.mem`. -/
@[expose] def BPreHullTrapInv (P_sub : Program) (m L : BitVec 64) (w : State) : Prop :=
  w.status = .Running ∧ keepBPreHull m w.pc = true ∧ w.readReg64 .lr = L ∧ P_sub.CodeLoaded w.mem

/-- **Whole-hull closed-trap impossibility (`bPreHull_trap_impossible`):** no `Steps P_ghost w sf`
    from `BPreHullTrapInv P_sub m L w` (over `bPreHullWords m resolve bPrePadWord`) can reach `sf`
    outside `keepBPreHull m` without `.Exception _` or `.Halted`:
    - on `bPreCodeRegion` (`[m, m+396) ∪ [m+400, m+956)`), `fetchMem_trapSafe` +
      `execInst_of_instrSafeInRegion` keeps `pc` in `keepBPreHull m` and preserves `lr = L`;
    - on `[m + 396, m + 400)` (`bPrePadWord = 0#32`), `bPrePad_fetchMem_none` gives
      `P_ghost.fetchMem s1.mem s1.pc = none`, ruling out `Step.exec` while `Step.halt_unmapped`
      contradicts `sf.status ≠ .Halted`. -/
theorem bPreHull_trap_impossible
    {P_ghost P_sub : Program} {m L : BitVec 64} {resolve : String → BitVec 64}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hL_in : keepBPreHull m L = true)
    (hreg_ext : ∀ pc : BitVec 64, keepBPreHull m pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    {w sf : State} (hsteps : Steps P_ghost w sf)
    (hout_sf : sf.status = .Running → keepBPreHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted)
    (hInv : BPreHullTrapInv P_sub m L w) : False := by
  induction hsteps with
  | refl _ =>
    have hfalse := hout_sf hInv.1; rw [hInv.2.1] at hfalse; exact Bool.noConfusion hfalse
  | @step s1 s2 _ h1 hrest ih =>
    rcases hInv with ⟨hrun1, hkeep1, hlr1, hCode1⟩
    have hCode2 : P_sub.CodeLoaded s2.mem := h1.codeLoaded hCode1
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact hnhalt_sf (by rw [ProofLib.Variant.Steps.eq_of_not_running hrest nofun])
    | extern_fault _ _ _ =>
      exact hnoex_sf _ (by rw [ProofLib.Variant.Steps.eq_of_not_running hrest nofun])
    | @extern f _ hext _ _ =>
      rcases hreg_ext s1.pc hkeep1 with hnone | ⟨f', hext', htrap⟩
      · rw [hnone] at hext; contradiction
      · rw [hext'] at hext; injection hext with hfeq; subst hfeq
        rcases htrap s1 hrun1 hlr1 with ⟨msg, hex⟩ | ⟨hrun2, hpc2, hlr2⟩
        · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex]; nofun)
          exact hnoex_sf msg (by rw [heq, hex])
        · exact ih hout_sf hnoex_sf hnhalt_sf ⟨hrun2, hpc2 ▸ hL_in, hlr2, hCode2⟩
    | @exec inst _ hfm =>
      rcases keepBPreHull_cases resolve hkeep1 with hcode | ⟨hlo, hhi⟩
      · obtain ⟨base, ws, off, hmem, _, hpc1, hsafe⟩ :=
          fetchMem_trapSafe (bPreCodeRegion_wordsSafe hres)
            (bPreCodeRegion_hasWords_of_bPreHull hhull)
            (bPreCodeRegion_codeLoaded_iff.mpr hCode1) hcode hfm
        have heval : P_ghost.evalInst inst s1 = execInst inst s1 :=
          evalInst_eq_execInst_of_not_isSvc0 hsafe.not_isSvc0 s1
        rcases execInst_of_instrSafeInRegion hmem hsafe hrun1 hpc1 with
          ⟨msg, hex⟩ | ⟨hrun2, hlr_eq, hpc_next⟩
        · have hex' : (P_ghost.evalInst inst s1).status = .Exception msg := heval ▸ hex
          have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex']; nofun)
          exact hnoex_sf msg (by rw [heq, hex'])
        · rw [heval] at ih hCode2
          have hkeep2 : keepBPreHull m (execInst inst s1).pc = true := by
            rcases hpc_next with hpc_ret | hkp
            · rw [hpc_ret, hlr1]; exact hL_in
            · exact keepBPreHull_of_bPreCodeRegion hkp
          exact ih hout_sf hnoex_sf hnhalt_sf ⟨hrun2, hkeep2, hlr_eq.trans hlr1, hCode2⟩
      · rw [bPrePad_fetchMem_none hhull hCode1 hlo hhi] at hfm; contradiction

/-- **Post-hook continuation `keepBPreHull m (u.readReg64 .lr) = false` (`H1` at `(f_u u).mem`):**
    Consumes `hCode_fu : P_sub.CodeLoaded (f_u u).mem` and `hrest : Steps P_ghost (f_u u) sf`. -/
theorem bPreHull_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {u sf : State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (htrap_u : keepBPreHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBPreHull m (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem) (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepBPreHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    keepBPreHull m (u.readReg64 .lr) = false := by
  cases hkeepL : keepBPreHull m (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    rcases htrap_u hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_fu, hpc_fu, hlr_fu⟩
    · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex]; nofun)
      exact hnoex_sf msg (by rw [heq, hex])
    · exact bPreHull_trap_impossible hhull hres hkeepL (hreg_ext hkeepL) hrest
        hout_sf hnoex_sf hnhalt_sf ⟨hrun_fu, hpc_fu ▸ hkeepL, hlr_fu, hCode_fu⟩

/-- Post-hook `Returned`-case `keepBPreHull m (u.readReg64 .lr) = false` (`H1` at `(f_u u).mem`). -/
theorem bPreHull_lr_trap_after_hook_returned
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {s0 u sf : State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (htrap_u : keepBPreHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBPreHull m (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem) (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running) (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr) (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false) :
    keepBPreHull m (u.readReg64 .lr) = false :=
  bPreHull_lr_trap_after_hook_ret hhull hres htrap_u hreg_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0) (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- Post-hook outcome theorem (`H1`: `P_sub.CodeLoaded (f_stub u).mem`). -/
theorem bPreHull_keepLr_false_after_hook_of_outcome_post
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {f_stub : State → State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreg_ext : ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBPreHull m L = true → TrapHook L f_stub)
    {s0 sf : State} (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State, Steps P_ghost (f_stub u) sf → u.status = .Running →
      P_sub.CodeLoaded (f_stub u).mem → keepBPreHull m (u.readReg64 .lr) = false :=
  fun _ hrest hrun_u hCode_fu =>
    bPreHull_lr_trap_after_hook_ret hhull hres (htrap_stub _) (hreg_ext _) hCode_fu hrest hrun_u
      (fun hr => hret_pc hr ▸ hlr_s0) hnoex_sf hnhalt_sf

/-- Direct `SubroutineOutcome` wrapper (`H1`: `P_sub.CodeLoaded (f_stub u).mem`). -/
theorem bPreHull_keepLr_false_after_hook_of_subroutineOutcome_post
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {f_stub : State → State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreg_ext : ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBPreHull m L = true → TrapHook L f_stub)
    {s0 sf : State} (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State, Steps P_ghost (f_stub u) sf → u.status = .Running →
      P_sub.CodeLoaded (f_stub u).mem → keepBPreHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact bPreHull_keepLr_false_after_hook_of_outcome_post hhull hres hreg_ext htrap_stub
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Post-hook outcome theorem (`H1` at `u.mem`: `P_sub.CodeLoaded u.mem` + `KeepsFrozen`). -/
theorem bPreHull_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {f_stub : State → State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreg_ext : ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBPreHull m L = true → TrapHook L f_stub)
    {s0 sf : State} (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State, Steps P_ghost (f_stub u) sf → u.status = .Running →
      P_sub.CodeLoaded u.mem → u.mem.KeepsFrozen (f_stub u).mem →
      keepBPreHull m (u.readReg64 .lr) = false :=
  fun u hrest hrun_u hCode_u hkf =>
    bPreHull_keepLr_false_after_hook_of_outcome_post hhull hres hreg_ext htrap_stub
      hlr_s0 hret_pc hnoex_sf hnhalt_sf u hrest hrun_u (hCode_u.of_keepsFrozen hkf)

/-- Direct `SubroutineOutcome` wrapper (`H1` at `u.mem`: `P_sub.CodeLoaded u.mem` + `KeepsFrozen`). -/
theorem bPreHull_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64} {f_stub : State → State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreg_ext : ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBPreHull m L = true → TrapHook L f_stub)
    {s0 sf : State} (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State, Steps P_ghost (f_stub u) sf → u.status = .Running →
      P_sub.CodeLoaded u.mem → u.mem.KeepsFrozen (f_stub u).mem →
      keepBPreHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact bPreHull_keepLr_false_after_hook_of_codeLoaded_u hhull hres hreg_ext htrap_stub
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Call-point `keepBPreHull m (u.readReg64 .lr) = false` (`H1`: `P_sub.CodeLoaded u.mem`). -/
theorem bPreHull_lr_trap_at_call_ret
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {u sf : State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (htrap_u : keepBPreHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBPreHull m (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u) (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf) (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepBPreHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    keepBPreHull m (u.readReg64 .lr) = false := by
  cases hsteps_u_sf with
  | refl => exact False.elim (hu_ne_sf hrun_u rfl)
  | @step _ v _ h1 hrest =>
    have hCode_v : P_sub.CodeLoaded v.mem := h1.codeLoaded hCode_u
    cases h1 with
    | exec _ hfm => unfold Program.fetchMem at hfm; rw [hext_u] at hfm; contradiction
    | halt_unmapped _ _ hext0 => rw [hext_u] at hext0; contradiction
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_sf _ (by rw [ProofLib.Variant.Steps.eq_of_not_running hrest nofun]))
    | @extern f _ hext _ _ =>
      rw [hext_u] at hext; injection hext with hfeq; subst hfeq
      exact bPreHull_lr_trap_after_hook_ret hhull hres htrap_u hreg_ext hCode_v hrest hrun_u
        hout_sf hnoex_sf hnhalt_sf

/-- Non-`.Running` terminal call-point `keepBPreHull m (u.readReg64 .lr) = false` (`H1`: `u.mem`). -/
theorem bPreHull_lr_trap_at_call
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {u sf : State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (htrap_u : keepBPreHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBPreHull m (u.readReg64 .lr) = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u) (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf) (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    keepBPreHull m (u.readReg64 .lr) = false :=
  bPreHull_lr_trap_at_call_ret hhull hres htrap_u hreg_ext hext_u hCode_u hsteps_u_sf hrun_u
    (fun hr => False.elim (hrun_sf hr)) (fun hr => False.elim (hrun_sf hr)) hnoex_sf hnhalt_sf

/-- At-stub outcome theorem (`H1`: `P_sub.CodeLoaded u.mem`, zero `s0.mem`; `MemmoveEntryGuard`
    discharged at C2 assembly via `Lib2LayoutFacts.lean:485` @ `a230f2671b`). -/
theorem bPreHull_keepLr_false_at_stub_of_outcome_u
    {P_ghost P_sub : Program} {m stubPc : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreg_ext : ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBPreHull m L = true → TrapHook L f_stub)
    {s0 sf : State} (hGuard0 : MemmoveEntryGuard m stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State, Steps P_ghost u sf → u.status = .Running → u.pc = stubPc →
      P_sub.CodeLoaded u.mem → keepBPreHull m (u.readReg64 .lr) = false :=
  fun _ hsteps_u_sf hrun_u hpc_u hCode_u =>
    bPreHull_lr_trap_at_call_ret hhull hres (htrap_stub _) (hreg_ext _) (hpc_u ▸ hext_stub) hCode_u
      hsteps_u_sf hrun_u
      (fun hr heq => hGuard0.2 ((hret_pc hr).symm.trans (heq.trans hpc_u)))
      (fun hr => hret_pc hr ▸ hGuard0.1) hnoex_sf hnhalt_sf

/-- At-stub `SubroutineOutcome` wrapper (`H1`: `P_sub.CodeLoaded u.mem`, zero `s0.mem`). -/
theorem bPreHull_keepLr_false_at_stub_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m stubPc : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreg_ext : ∀ L : BitVec 64, keepBPreHull m L = true →
      ∀ pc : BitVec 64, keepBPreHull m pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBPreHull m L = true → TrapHook L f_stub)
    {s0 sf : State} (hGuard0 : MemmoveEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State, Steps P_ghost u sf → u.status = .Running → u.pc = stubPc →
      P_sub.CodeLoaded u.mem → keepBPreHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact bPreHull_keepLr_false_at_stub_of_outcome_u hhull hres hreg_ext hext_stub htrap_stub
    hGuard0 hret_pc hnoex_sf hnhalt_sf

/-- Ready-to-apply 3-entry (`C4` + `F1`) + post-hook `CodeLoaded` (`H1`) `SubroutineOutcome`
    corollary for plain `f3EmptyMemmoveGhostHook` (premises copied verbatim from
    `Lib2LayoutFacts.lean:392-402, :346-353, :355-362` @ `a230f2671b`, **NOT imported**). -/
theorem f3EmptyMemmoveGhostHook_keepLr_false_after_hook_of_subroutineOutcome_post
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    {resolve : String → BitVec 64} {extOf : String → Option (State → State)}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hcov : KeepCoversBPreHull keepR m)
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" = some (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    {s0 sf : State} (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u) sf →
      u.status = .Running →
      P_sub.CodeLoaded (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem →
      keepBPreHull m (u.readReg64 .lr) = false :=
  bPreHull_keepLr_false_after_hook_of_subroutineOutcome_post hhull hres
    (bPreHull_reg_ext_forall_of_entries hOffEntries hEntry
      (fun f hf _ hL => by
        rcases hMemmoveExt with hn | hs
        · rw [hn] at hf; contradiction
        · rw [hs] at hf; injection hf with hfeq; subst hfeq
          exact trapHook_f3EmptyMemmoveGhostHook_of_cover P_sub _ hcov hL)
      hMemcpyTrap hMemsetTrap)
    (fun _ hL => trapHook_f3EmptyMemmoveGhostHook_of_cover P_sub _ hcov hL) hlr_s0 hout

/-- Ready-to-apply 3-entry (`C4` + `F1`) + post-hook `CodeLoaded` (`H1`) `SubroutineOutcome`
    corollary for `K`-narrowed `f3EmptyMemmoveGhostHookK` (citing `Lib2LayoutFacts.lean:392-402,
    :346-353, :355-362` @ `a230f2671b`, **NOT imported**). -/
theorem f3EmptyMemmoveGhostHookK_keepLr_false_after_hook_of_subroutineOutcome_post
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    {resolve : String → BitVec 64} {extOf : String → Option (State → State)}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hcov : KeepCoversBPreHull keepR m)
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" = some (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff)))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    {s0 sf : State} (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u) sf →
      u.status = .Running →
      P_sub.CodeLoaded (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff) u).mem →
      keepBPreHull m (u.readReg64 .lr) = false :=
  bPreHull_keepLr_false_after_hook_of_subroutineOutcome_post hhull hres
    (bPreHull_reg_ext_forall_of_entries hOffEntries hEntry
      (fun f hf _ hL => by
        rcases hMemmoveExt with hn | hs
        · rw [hn] at hf; contradiction
        · rw [hs] at hf; injection hf with hfeq; subst hfeq
          exact trapHook_f3EmptyMemmoveGhostHookK_of_cover P_sub _ hcov hL)
      hMemcpyTrap hMemsetTrap)
    (fun _ hL => trapHook_f3EmptyMemmoveGhostHookK_of_cover P_sub _ hcov hL) hlr_s0 hout

/-- Ready-to-apply 3-entry (`C4` + `F1`) at-stub `SubroutineOutcome` corollary (`H1`: `u.mem`,
    zero `s0.mem`) for `f3EmptyMemmoveGhostHook{,K}` (`Lib2LayoutFacts.lean` @ `a230f2671b`
    `:392-402, :346-353, :355-362, :485`, **NOT imported**). -/
theorem f3EmptyMemmoveGhostHook_keepLr_false_at_stub_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc : BitVec 64}
    {resolve : String → BitVec 64} {extOf : String → Option (State → State)}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hcov : KeepCoversBPreHull keepR m)
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" = some (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff)))
    {s0 sf : State} (hGuard0 : MemmoveEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State, Steps P_ghost u sf → u.status = .Running → u.pc = stubPc →
      P_sub.CodeLoaded u.mem → keepBPreHull m (u.readReg64 .lr) = false :=
  bPreHull_keepLr_false_at_stub_of_subroutineOutcome_u hhull hres
    (bPreHull_reg_ext_forall_of_entries hOffEntries hEntry
      (fun f hf _ hL => by
        rcases hMemmoveExt with hn | hs
        · rw [hn] at hf; contradiction
        · rw [hs] at hf; injection hf with hfeq; subst hfeq
          exact trapHook_f3EmptyMemmoveGhostHook_of_cover P_sub _ hcov hL)
      hMemcpyTrap hMemsetTrap)
    hext_stub (fun _ hL => trapHook_f3EmptyMemmoveGhostHook_of_cover P_sub _ hcov hL) hGuard0 hout

private theorem f3EmptyMemmoveGhostHook_keepsFrozen_of_noException
    {keepR : BitVec 64 → Bool} {P_sub : Program}
    {m : BitVec 64} {resolve : String → BitVec 64} {padWord : BitVec 32} {u : State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord))
    (hres : resolve "memcpy" = m) (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).status ≠ .Exception msg) :
    u.mem.KeepsFrozen (f3EmptyMemmoveGhostHook keepR P_sub (m + bPreMemmoveByteOff) u).mem := by
  classical
  by_cases hAct : ActiveRealPre masterMemmoveSpec u
  · obtain ⟨_, hsp, x, R, hpre⟩ := id hAct
    exact (f3EmptyMemmoveGhostHook_master_ok hsvc_sub hsub_no hhull hres x R u hrun hpre hsp).1
  · exfalso
    apply hnoex "ghost-hook precondition violated"
    rw [f3EmptyMemmoveGhostHook_eq, memmoveGhostFn]; unfold linkedCallHook; simp [hAct]

/-- **End-to-end Stage A `GhostExternReplaysOn keep_any` from subroutine outcome (`H1` + `C4` + `F1`):**
    Closes `MemmoveGhostReplays.f3EmptyMemmoveGhostHook_replaysOn_of_lrOut` for `keepR :=
    keepBPreHull m` and `padWord := bPrePadWord` using `codeLoaded_of_stripExecOutside` at `u.mem`
    (`H1`, zero `s0.mem` `CodeLoaded`) + `f3EmptyMemmoveGhostHook_keepsFrozen_of_noException` +
    verbatim 3-entry `Lib2LayoutFacts` `@ a230f2671b` (`:392-402, :346-353, :355-362`, **NOT imported**). -/
theorem f3EmptyMemmoveGhostHook_replaysOn_of_outcome
    (keep_any : BitVec 64 → Bool) {InvMem : Memory → Prop}
    {P_ghost P_real P_sub : Program} {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHook (keepBPreHull m) P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (ProofLib.stripExecOutside (keepBPreHull m) mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn (keepBPreHull m) emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf')
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" =
        some (f3EmptyMemmoveGhostHook (keepBPreHull m) P_sub (m + bPreMemmoveByteOff)))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg) (hnhalt_sf : sf.status ≠ .Halted) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf :=
  f3EmptyMemmoveGhostHook_replaysOn_of_lrOut keep_any hghost_stub hother hreal_fr
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
    (fun u _ hpost _ hrun hnoex hfr hinv =>
      bPreHull_keepLr_false_after_hook_of_codeLoaded_u hhull hres
        (bPreHull_reg_ext_forall_of_entries hOffEntries hEntry
          (fun f hf _ hL => by
            rcases hMemmoveExt with hn | hs
            · rw [hn] at hf; contradiction
            · rw [hs] at hf; injection hf with hfeq; subst hfeq
              exact trapHook_f3EmptyMemmoveGhostHook P_sub _ hL)
          hMemcpyTrap hMemsetTrap)
        (fun _ hL => trapHook_f3EmptyMemmoveGhostHook P_sub _ hL)
        hlr_s0 hret_pc hnoex_sf hnhalt_sf u hpost hrun
        (codeLoaded_of_stripExecOutside (hInvLoaded u.mem hfr hinv))
        (f3EmptyMemmoveGhostHook_keepsFrozen_of_noException hsvc_sub hsub_no hhull hres hrun hnoex))

/-- Direct `SubroutineOutcome` wrapper for `f3EmptyMemmoveGhostHook_replaysOn_of_outcome`. -/
theorem f3EmptyMemmoveGhostHook_replaysOn_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    (keep_any : BitVec 64 → Bool) {InvMem : Memory → Prop}
    {P_ghost P_real P_sub : Program} {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHook (keepBPreHull m) P_sub (m + bPreMemmoveByteOff)))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      P_sub.CodeLoaded (ProofLib.stripExecOutside (keepBPreHull m) mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn (keepBPreHull m) emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf')
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" =
        some (f3EmptyMemmoveGhostHook (keepBPreHull m) P_sub (m + bPreMemmoveByteOff)))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyMemmoveGhostHook_replaysOn_of_outcome keep_any hghost_stub hother hreal_fr
    hsvc_sub hsub_no hhull hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
    hOffEntries hEntry hMemmoveExt hMemcpyTrap hMemsetTrap hlr_s0 hret_pc hnoex_sf hnhalt_sf


/-- Ready-to-apply 3-entry (`C4` + `F1`) at-stub `SubroutineOutcome` corollary (`H1`: `u.mem`,
    zero `s0.mem`) for `K`-narrowed `f3EmptyMemmoveGhostHookK` (`Lib2LayoutFacts.lean` @
    `a230f2671b` `:392-402, :346-353, :355-362, :485`, **NOT imported**). -/
theorem f3EmptyMemmoveGhostHookK_keepLr_false_at_stub_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc : BitVec 64}
    {resolve : String → BitVec 64} {extOf : String → Option (State → State)}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hres : resolve "memcpy" = m := by rfl)
    (hcov : KeepCoversBPreHull keepR m)
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" = some (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff)))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyMemmoveGhostHookK keepR P_sub (m + bPreMemmoveByteOff)))
    {s0 sf : State} (hGuard0 : MemmoveEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State, Steps P_ghost u sf → u.status = .Running → u.pc = stubPc →
      P_sub.CodeLoaded u.mem → keepBPreHull m (u.readReg64 .lr) = false :=
  bPreHull_keepLr_false_at_stub_of_subroutineOutcome_u hhull hres
    (bPreHull_reg_ext_forall_of_entries hOffEntries hEntry
      (fun f hf _ hL => by
        rcases hMemmoveExt with hn | hs
        · rw [hn] at hf; contradiction
        · rw [hs] at hf; injection hf with hfeq; subst hfeq
          exact trapHook_f3EmptyMemmoveGhostHookK_of_cover P_sub _ hcov hL)
      hMemcpyTrap hMemsetTrap)
    hext_stub (fun _ hL => trapHook_f3EmptyMemmoveGhostHookK_of_cover P_sub _ hcov hL) hGuard0 hout

/-- Pure-carrier (`P_sub := pureWordsProg m (bPreHullWords m resolve bPrePadWord)`) `SubroutineOutcome`
    specialization of `f3EmptyMemmoveGhostHook_replaysOn_of_subroutineOutcome` (`H1` + `C4` + `F1`). -/
theorem f3PureMemmoveGhostHook_replaysOn_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    (keep_any : BitVec 64 → Bool) {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {s0 sf : State}
    {stubPc m : BitVec 64} {resolve : String → BitVec 64}
    {extOf : String → Option (State → State)}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (f3PureMemmoveGhostHook (keepBPreHull m) m resolve bPrePadWord))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hres : resolve "memcpy" = m := by rfl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (m + bPreMemmoveByteOff))
    (hInvLoaded : ∀ mem : Memory, ExecFrozen mem → InvMem mem →
      (pureWordsProg m (bPreHullWords m resolve bPrePadWord)).CodeLoaded
        (ProofLib.stripExecOutside (keepBPreHull m) mem))
    (hInvKf : ∀ mem mem' : Memory, InvMem mem → mem.KeepsFrozen mem' → InvMem mem')
    (hLiftVis : ∀ u sf' : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn (keepBPreHull m) emptyStdProg (u.setPC (m + bPreMemmoveByteOff)) sf' →
      Steps P_real (u.setPC (m + bPreMemmoveByteOff)) sf')
    (hOffEntries : ∀ {pc : BitVec 64}, keepBPreHull m pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map resolve → P_ghost.externAt? pc = none)
    (hEntry : ∀ {sym : String}, sym ∈ ["memmove", "memcpy", "memset"] →
      P_ghost.externAt? (resolve sym) = extOf sym)
    (hMemmoveExt : extOf "memmove" = none ∨
      extOf "memmove" = some (f3PureMemmoveGhostHook (keepBPreHull m) m resolve bPrePadWord))
    (hMemcpyTrap : ∀ f, extOf "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ f, extOf "memset" = some f → ∀ L, TrapHook L f)
    (hlr_s0 : keepBPreHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    GhostExternReplaysOn keep_any (fun u => InvMem u.mem) P_ghost P_real s0 sf :=
  f3EmptyMemmoveGhostHook_replaysOn_of_subroutineOutcome keep_any hghost_stub hother hreal_fr
    rfl (pureWordsProg_externAt_none m (bPreHullWords m resolve bPrePadWord))
    (pureWordsProg_bPreHull_hasWords m resolve bPrePadWord)
    hres hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
    hOffEntries hEntry hMemmoveExt hMemcpyTrap hMemsetTrap hlr_s0 hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrap
