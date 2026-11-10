/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn -- proof-setup: allow-public-import

/-!
# Local `keepMemsetBlk21 lr = false` from Subroutine Outcomes (`HooksDehook.MemsetKeepLrOfOutcome`)

Delivers Card `H-C8` **D2** (`rev_q8.md` §1b–§1d): under the generalized D1(c) `hTraj` context
(`Guard s0`, `sf.status = .Running → sf.pc = s0.readReg64 .lr`, `∀ msg, sf.status ≠ .Exception msg`,
`sf.status ≠ .Halted`, or the full `SubroutineOutcome`), proves that every intermediate call `u`
(`Steps P_ghost s0 u`, `Steps P_ghost u sf`, `u.status = .Running`) into the `memset` ghost has
`keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`:

1. **Entry-state guards (`MemsetEntryGuard`, `F3MemsetEntryGuard`, `MemsetMixedEntryGuard`):**
   `MemsetEntryGuard mmpl stubPc s0 := keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
   s0.readReg64 .lr ≠ stubPc` (specialized at `stubPc := mpl.ρ "memset"` by `F3MemsetEntryGuard`).
2. **Single-stub `memset` call-point `lr` discharge (`memset_keepLr_false_of_outcome_memset`):**
   Splits on `sf.status = .Running`:
   - `Returned` (`sf.status = .Running`, `sf.pc = s0.readReg64 .lr`): discharged by
     `MemsetLrTrapRet.blk21_lr_trap_false_memset_returned` + `MemsetEntryGuard`;
   - non-`Running` (`Exited`, `Panicked`, `OutOfMemory`, `Signaled`): discharged by
     `MemsetLrTrap.blk21_lr_trap_false_nonRunning` (or `(A2)`
     `MemsetLrTrapRet.blk21_lr_trap_false_mixed_nonRunning` when `P_ghost` carries other trap-safe
     ghosts).
3. **At-stub (`P_real`-independent) & mixed-table `(A2)` call-point `lr` discharge:**
   `memset_keepLr_false_at_stub_of_outcome` (needs only `u.pc = stubPc` and zero single-stub
   mismatch assumption on `P_real`) and `memset_keepLr_false_of_outcome_mixed`, plus direct
   `SubroutineOutcome` corollaries and the single-stub `memset`-only transfer combiner
   `block617TransferFixedG_memsetNarrow_of_replaysOn` (note `rev_c6` F2 / `rev_c8` T2: single
   mismatch, hook's `P_real` = transfer's `P_real`, so `memset`-only pass, **not** the K CLI pass).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open CryptoVerification.SignalSession (CliHooks Inputs cliProcessInputs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostExternReplaysOn StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn
   subroutineOutcome_running_pc_and_noFault)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (linkedCallHook_fs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
  (keepMemsetBlk21 memsetGhostHook memsetGhostHookBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
  (ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrap
  (blk21_lr_trap_false_nonRunning)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
  (Blk21TrapHook blk21TrapHook_memsetGhostHook blk21_lr_trap_at_call_ret
   blk21_lr_trap_false_memset_returned blk21_lr_trap_false_mixed_nonRunning
   blk21_lr_trap_false_mixed_returned blk21_lr_trap_false_single_returned)

/-! ## 1. Real-Side Entry-State `lr` Guards (`MemsetEntryGuard`, `F3MemsetEntryGuard`) -/

/-- Variant-A real-side entry guard at `s0`: the caller's link register `s0.readReg64 .lr` lies
    outside `mallocng` block `21` (`memset`, 260 B) and is distinct from `stubPc`. -/
@[expose] def MemsetEntryGuard
    (mmpl : Obj.MultiPlacement) (stubPc : BitVec 64) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

/-- Specialization of `MemsetEntryGuard` to the `libsignalSessionLib` external `"memset"` stub
    symbol `mpl.ρ "memset"`. -/
@[expose] def F3MemsetEntryGuard (mpl mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  MemsetEntryGuard mmpl (mpl.ρ "memset") s0

/-- Mixed-pass `(A2)` generalization of `MemsetEntryGuard`: `s0.readReg64 .lr` lies outside `blk21`
    and is not a mismatched extern stub between `P_ghost` and `P_real`. -/
@[expose] def MemsetMixedEntryGuard
    (P_ghost P_real : Program) (mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
  P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)

/-- Any single-stub `MemsetEntryGuard mmpl stubPc s0` implies `MemsetMixedEntryGuard` whenever
    `P_ghost` and `P_real` agree outside `stubPc`. -/
theorem MemsetEntryGuard.toMixed
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64} {s0 : State}
    (hother : ∀ pc : BitVec 64, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hG : MemsetEntryGuard mmpl stubPc s0) :
    MemsetMixedEntryGuard P_ghost P_real mmpl s0 :=
  ⟨hG.1, hother (s0.readReg64 .lr) hG.2⟩

/-! ## 2. Call-Point `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` from Outcome Facts -/

/-- **D2 single-stub `memsetGhostHook` theorem (`memset_keepLr_false_of_outcome_memset`):**
    Under the D1(c) `hTraj` premises (`MemsetEntryGuard mmpl stubPc s0`,
    `sf.status = .Running → sf.pc = s0.readReg64 .lr`, `∀ msg, sf.status ≠ .Exception msg`,
    `sf.status ≠ .Halted`) and `blk21` extern-freeness on `P_ghost`, every intermediate mismatched
    call `u` along `s0 →* u →* sf` satisfies `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`:
    - `Returned` (`sf.status = .Running`): `MemsetLrTrapRet.blk21_lr_trap_false_memset_returned`,
    - non-`Running` (`sf.status ≠ .Running`): `MemsetLrTrap.blk21_lr_trap_false_nonRunning`.
    **Caveat (`rev_c6` F2 / `rev_c8` T2):** Requires a single extern mismatch (`hmis_stub`), so
    this covers a `memset`-only pass, **not** the simultaneous K CLI pass alongside the 7 K ghosts
    (use `memset_keepLr_false_at_stub_of_outcome` or `memset_keepLr_false_of_outcome_mixed` when
    multiple stubs differ). -/
theorem memset_keepLr_false_of_outcome_memset
    {P_ghost P_real P_hookReal P_sub : Program} {mmpl : Obj.MultiPlacement}
    {stubPc entryTarget : BitVec 64}
    (hblk21_no : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true → P_ghost.externAt? pc = none)
    (hmis_stub : ∀ pc : BitVec 64, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHook (keepMemsetBlk21 mmpl) P_hookReal P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetEntryGuard mmpl stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  by_cases hrun_sf : sf.status = .Running
  · exact blk21_lr_trap_false_memset_returned
      (fun pc hpc => Or.inl (hblk21_no pc hpc))
      hmis_stub hext_stub hc_codeLoaded
      hrun_sf (hret_pc hrun_sf) hGuard0.1 hGuard0.2
  · exact blk21_lr_trap_false_nonRunning
      (fun _ ha => ha)
      (fun pc hpc => Or.inl (hblk21_no pc hpc))
      (fun pc hmis => hmis_stub pc hmis ▸ hext_stub)
      hc_codeLoaded hrun_sf hnoex_sf hnhalt_sf

/-- **`(A2)`-generalized single-stub `memsetGhostHook` theorem (`memset_keepLr_false_of_outcome_memset_ext`):**
    Relaxes `hblk21_no` to `hblk21_ext` (allowing trap-safe hooks inside `blk21`).
    **Caveat (`rev_c6` F2 / `rev_c8` T2):** Requires a single extern mismatch (`hmis_stub`), so
    this covers a `memset`-only pass, **not** the simultaneous K CLI pass. -/
theorem memset_keepLr_false_of_outcome_memset_ext
    {P_ghost P_real P_hookReal P_sub : Program} {mmpl : Obj.MultiPlacement}
    {stubPc entryTarget : BitVec 64}
    (hblk21_ext : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_stub : ∀ pc : BitVec 64, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHook (keepMemsetBlk21 mmpl) P_hookReal P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetEntryGuard mmpl stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  by_cases hrun_sf : sf.status = .Running
  · exact blk21_lr_trap_false_memset_returned
      hblk21_ext hmis_stub hext_stub hc_codeLoaded
      hrun_sf (hret_pc hrun_sf) hGuard0.1 hGuard0.2
  · exact blk21_lr_trap_false_mixed_nonRunning
      hblk21_ext
      (fun pc hmis => ⟨_, hmis_stub pc hmis ▸ hext_stub,
        fun _ hL => blk21TrapHook_memsetGhostHook P_hookReal P_sub entryTarget hL⟩)
      hc_codeLoaded hrun_sf hnoex_sf hnhalt_sf

/-- **Generic single-stub trap-hook theorem (`memset_keepLr_false_of_outcome_single`):**
    Applies to any ghost hook `f_stub` at `stubPc` satisfying
    `∀ L, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_stub` (including `memsetGhostHook`,
    `f3MemsetGhostHookNarrow`, `h2k_memsetGhostHookNarrow`, and `memsetGhostHookK`).
    **Caveat (`rev_c6` F2 / `rev_c8` T2):** Requires a single extern mismatch (`hmis_stub`), so
    this covers a `memset`-only pass, **not** the simultaneous K CLI pass (use
    `memset_keepLr_false_at_stub_of_outcome` for a `P_real`-independent per-stub statement). -/
theorem memset_keepLr_false_of_outcome_single
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hblk21_ext : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_stub : ∀ pc : BitVec 64, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetEntryGuard mmpl stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  by_cases hrun_sf : sf.status = .Running
  · exact blk21_lr_trap_false_single_returned
      hblk21_ext hmis_stub hext_stub htrap_stub hc_codeLoaded
      hrun_sf (hret_pc hrun_sf) hGuard0.1 hGuard0.2
  · exact blk21_lr_trap_false_mixed_nonRunning
      hblk21_ext
      (fun pc hmis => ⟨f_stub, hmis_stub pc hmis ▸ hext_stub, htrap_stub⟩)
      hc_codeLoaded hrun_sf hnoex_sf hnhalt_sf

/-- **`(A2)` mixed-table call-point `lr` theorem (`memset_keepLr_false_of_outcome_mixed`):**
    Supports simultaneous de-hooking of narrow `memset` alongside all 7 K-narrowed F3 ghosts
    (`h2k_ghFixedK_blk21TrapHook`), combining `blk21_lr_trap_false_mixed_returned` and
    `blk21_lr_trap_false_mixed_nonRunning`. -/
theorem memset_keepLr_false_of_outcome_mixed
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk21_ext : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_trap : ∀ pc : BitVec 64, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetMixedEntryGuard P_ghost P_real mmpl s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  by_cases hrun_sf : sf.status = .Running
  · exact blk21_lr_trap_false_mixed_returned
      hblk21_ext hmis_trap hc_codeLoaded hrun_sf (hret_pc hrun_sf) hGuard0.1 hGuard0.2
  · exact blk21_lr_trap_false_mixed_nonRunning
      hblk21_ext hmis_trap hc_codeLoaded hrun_sf hnoex_sf hnhalt_sf

/-- **At-stub (`P_real`-independent) call-point `lr` theorem (`memset_keepLr_false_at_stub_of_outcome`):**
    At every intermediate `.Running` state `u` (`Steps P_ghost s0 u`, `Steps P_ghost u sf`) with
    `u.pc = stubPc` where `P_ghost.externAt? stubPc = some f_stub` is a `Blk21TrapHook`,
    `MemsetEntryGuard mmpl stubPc s0` + the D1(c) terminal outcome facts directly imply
    `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` — with **no** single-stub mismatch requirement
    on any `P_real`. -/
theorem memset_keepLr_false_at_stub_of_outcome
    {P_ghost : Program} {mmpl : Obj.MultiPlacement}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hblk21_ext : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetEntryGuard mmpl stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  exact blk21_lr_trap_at_call_ret htrap_stub hblk21_ext
    (hpc_u ▸ hext_stub)
    (hsteps_s0_u.codeLoaded hc_codeLoaded)
    hsteps_u_sf hrun_u
    (fun hrun_sf heq_pc => hGuard0.2 ((hret_pc hrun_sf).symm.trans (heq_pc.trans hpc_u)))
    (fun hrun_sf => hret_pc hrun_sf ▸ hGuard0.1)
    hnoex_sf hnhalt_sf

/-! ## 3. Direct `SubroutineOutcome` & D1(c) `Block617TransferFixedHypG` Corollaries -/

/-- Direct `SubroutineOutcome` wrapper for `memset_keepLr_false_of_outcome_memset` (consumes
    `hout : SubroutineOutcome spec_ghost x R s0 sf` from `block617TransferFixedG_of_replaysOn_outcome`).
    **Caveat (`rev_c6` F2 / `rev_c8` T2):** Single extern mismatch (`hmis_stub`), so `memset`-only
    pass, **not** the K CLI pass. -/
theorem memset_keepLr_false_of_subroutineOutcome_memset
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_real P_hookReal P_sub : Program} {mmpl : Obj.MultiPlacement}
    {stubPc entryTarget : BitVec 64}
    (hblk21_no : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true → P_ghost.externAt? pc = none)
    (hmis_stub : ∀ pc : BitVec 64, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc =
      some (memsetGhostHook (keepMemsetBlk21 mmpl) P_hookReal P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetEntryGuard mmpl stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact memset_keepLr_false_of_outcome_memset
    hblk21_no hmis_stub hext_stub hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-- Direct `SubroutineOutcome` wrapper for `memset_keepLr_false_at_stub_of_outcome`. -/
theorem memset_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {mmpl : Obj.MultiPlacement}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hblk21_ext : ∀ pc : BitVec 64, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hGuard0 : MemsetEntryGuard mmpl stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepMemsetBlk21 mmpl (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact memset_keepLr_false_at_stub_of_outcome
    hblk21_ext hext_stub htrap_stub hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-- **Single-stub `memset`-only `Block617TransferFixedHypG` combiner (`block617TransferFixedG_memsetNarrow_of_replaysOn`):**
    Combines D1(c) (`block617TransferFixedG_of_replaysOn` at `keep := keepMemsetBlk21 mmpl`),
    D2 (`memset_keepLr_false_of_outcome_memset_ext` for `hlr_calls`), and H-C6's
    `ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret` (preserving both `InvMem` and
    `PredFs` since `memsetGhostHook` leaves `u.fs` unchanged) to close `Block617TransferFixedHypG`
    under `Guard := MemsetEntryGuard mmpl stubPc`.
    **Caveat (`rev_c6` F2 / `rev_c8` T2):** Assumes a single extern mismatch (`hother`) and sets
    the hook's `P_real` equal to the transfer's `W`-dependent `P_real` (`cliProgExtPlacedAt mpl ER 617 W`),
    so this covers a **`memset`-only** transfer pass — **not** the K CLI pass alongside the 7 K
    ghosts or a `W`-independent `cliGhostExterns gh` table. -/
theorem block617TransferFixedG_memsetNarrow_of_replaysOn
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart stubPc : BitVec 64} {stk : Nat}
    (InvMem : Memory → Prop) (PredFs : FsState → Prop)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hghost_stub : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? stubPc =
        some (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) (cliProgExtPlacedAt mpl ER 617 W) mmpl))
    (hother : ∀ (W : CliHooks) (pc : BitVec 64), pc ≠ stubPc →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc =
        (cliProgExtPlacedAt mpl ER 617 W).externAt? pc)
    (hreal_stub_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl ER 617 W).externAt? stubPc = none)
    (hreal_blk21_none : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hblk21_ext : ∀ (W : CliHooks) (pc : BitVec 64),
      keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn InvMem (cliProgExtPlacedAt mpl ER 617 W) stubPc (mmpl.base 21))
    (hRealHooks : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem → PredFs u.fs →
        ExecFrozen (f u).mem ∧ PredFs (f u).fs)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    Block617TransferFixedHypG mpl mmpl EG ER (MemsetEntryGuard mmpl stubPc)
      CodeOk_ghost CodeOk_real libcAddr brkStart stk := by
  have hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none := by
    intro W pc hgn
    by_cases hpc : pc = stubPc
    · subst hpc; exact hreal_stub_none W
    · rw [← hother W pc hpc]; exact hgn
  refine block617TransferFixedG_of_replaysOn (keepMemsetBlk21 mmpl) InvMem PredFs
    hNoNewHooks hCode hGhostCL hFr0 hInv0 hInvStable hFs0
    fun W _i s0 sf hGuard0 hReal0 _ _ _ _ hret_pc hnoex_sf hnhalt_sf => ?_
  let P_ghost := cliProgExtPlacedAt mpl EG 617 W
  let P_real := cliProgExtPlacedAt mpl ER 617 W
  have hmis_stub : ∀ pc : BitVec 64, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc :=
    fun pc hmis => Classical.byContradiction fun hne => hmis (hother W pc hne)
  have hc_codeLoaded : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem :=
    hInvLoaded s0.mem (hFr0 s0.mem hReal0) (hInv0 s0.mem hReal0)
  have hRep := ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
    (InvMem := InvMem) (P_ghost := P_ghost) (P_real := P_real) (mmpl := mmpl) (stubPc := stubPc)
    (hblk21_ext W) rfl (hreal_blk21_none W) (hreal_stub_none W) (hStub W) hInvLoaded hInvStable
    (fun hrun_sf => hret_pc hrun_sf ▸ hGuard0.1) hnoex_sf hnhalt_sf
  have hReplays : GhostExternReplaysOn (keepMemsetBlk21 mmpl)
      (fun u => InvMem u.mem ∧ PredFs u.fs) P_ghost P_real s0 sf := by
    intro pc f hgf
    by_cases hpc : pc = stubPc
    · subst hpc
      rw [hghost_stub W] at hgf
      injection hgf with hfeq
      subst hfeq
      refine Or.inr ⟨hRep.1, ?_⟩
      intro u _ hrest hpc_u hrun_u hnoex_u hkf_u hfr_u _ ⟨hInv_u, hFs_u⟩
      obtain ⟨hsteps_u, hfr', hInv'⟩ :=
        hRep.2 u hrest hpc_u hrun_u hnoex_u hkf_u hfr_u hInv_u
      have hfs_eq : (memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) P_real mmpl u).fs = u.fs :=
        linkedCallHook_fs_eq u
      exact ⟨hsteps_u, hfr', hInv', hfs_eq ▸ hFs_u⟩
    · refine Or.inl ⟨(hother W pc hpc).symm.trans hgf, ?_⟩
      intro u _ _ _ hrun_u _ hkf_u hfr_u ⟨hInv_u, hFs_u⟩
      have hr : P_real.externAt? pc = some f := (hother W pc hpc).symm.trans hgf
      obtain ⟨hfr', hFs'⟩ := hRealHooks W pc f hr u hrun_u hfr_u hInv_u hFs_u
      exact ⟨hfr', hInvStable u.mem (f u).mem hInv_u hkf_u, hFs'⟩
  refine ⟨hReplays, ?_, ?_⟩
  · intro z hs1 hs2 hrun_z hgn hfm hfr_z hInv_z hFs_z
    exact hSvcFs W s0 sf z hs1 hs2 hrun_z hgn hfm hfr_z hInv_z hFs_z
  · exact memset_keepLr_false_of_outcome_memset_ext
      (hblk21_ext W) hmis_stub (hghost_stub W) hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetKeepLrOfOutcome
