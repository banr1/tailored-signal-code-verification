/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import

/-!
# Closed-`lr` Trap Corollaries for `SharedSecret::drop` (`HooksDehook.SharedSecretDropLrTrap`)

Row 2 post-hook and at-stub `SubroutineOutcome` corollaries for Card **D-d** (`dd_dalek_lrtrap.md`),
over the 256-byte (`64`-word) contiguous hull `sharedSecretDropHullWords` at hull base `m`
(`<MontgomeryPoint as Zeroize>::zeroize` at `m`, hooked `<SharedSecret as Drop>::drop` entry at
`m + sharedSecretDropEntryOff`):
- Generic post-hook (`P_sub.CodeLoaded u.mem` at `u` per `H1`, plus `s0.mem` trajectory companion)
  and at-stub `SubroutineOutcome` trap corollaries.
- Parametric `sharedSecretDropHull_reg_ext_of_entry_excluded` (`entries : List (BitVec 64)`) and
  drop-entry specialization `sharedSecretDropHull_reg_ext_of_dropEntry_excluded`
  (`entries = [m + sharedSecretDropEntryOff]`).
- Six entry-excluded (`F1`) `f3EmptySharedSecretDropGhostHook{,K}` wrappers taking hull base `m`
  (`D3`), `keepR` covering the whole 64-word `keepSharedSecretDropHull m`, and hooked entry
  `m + sharedSecretDropEntryOff` ONLY (never excluding unhooked `m`), matching STARTUP's
  `f3Row_ghostProg617_externAt_none_of_ne_entry`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropLrTrap

open Arm64 ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapHook
  lr_trap_at_call_ret lr_trap_at_call keepLr_false_at_stub_of_outcome
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (
  lr_trap_after_hook_ret
  keepLr_false_after_hook_of_outcome
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  sharedSecretDropHullWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (
  sharedSecretDropEntryOff
  f3EmptySharedSecretDropGhostHook f3EmptySharedSecretDropGhostHookK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap (
  keepSharedSecretDropHull
  sharedSecretDropHullRegion
  keepOf_sharedSecretDropHullRegion_apply
  sharedSecretDropHull_regionWordsSafe
  sharedSecretDropHullRegion_hasWords_of_hasWords
  sharedSecretDropHullRegion_codeLoaded_iff
  SharedSecretDropEntryGuard
  sharedSecretDropEntryGuard_iff_trapEntryGuard
  trapHook_f3EmptySharedSecretDropGhostHook_of_cover
  trapHook_f3EmptySharedSecretDropGhostHookK_of_cover
)

/-! ## 1. Post-Hook & At-Stub Trap Corollaries for `SharedSecret::drop` (`keepSharedSecretDropHull`) -/

theorem sharedSecretDropHull_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {m : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (htrap_u : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      ∀ pc, keepSharedSecretDropHull m pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepSharedSecretDropHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  rw [← keepOf_sharedSecretDropHullRegion_apply m]
  exact lr_trap_after_hook_ret
    (sharedSecretDropHull_regionWordsSafe m)
    (sharedSecretDropHullRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL) pc
        (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hkp))
    (sharedSecretDropHullRegion_codeLoaded_iff.mpr hCode_fu)
    hrest hrun_u
    (fun hr => (keepOf_sharedSecretDropHullRegion_apply m _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

theorem sharedSecretDropHull_lr_trap_after_hook_returned
    {P_ghost P_sub : Program} {m : BitVec 64} {f_u : State → State} {s0 u sf : State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (htrap_u : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      ∀ pc, keepSharedSecretDropHull m pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false) :
    keepSharedSecretDropHull m (u.readReg64 .lr) = false :=
  sharedSecretDropHull_lr_trap_after_hook_ret hHas htrap_u hreg_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- **Card-`c` `InvS u` post-hook theorem
    (`sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u`):**
    Consumes `P_sub.CodeLoaded u.mem` at `u` + `u.mem.KeepsFrozen (f_stub u).mem` (per `H1`). -/
theorem sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {m : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hreg_ext : ∀ pc : BitVec 64, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  intro u hc_u hsteps_fu_sf hrun_u hkf
  exact sharedSecretDropHull_lr_trap_after_hook_ret hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (hc_u.of_keepsFrozen hkf)
    hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

theorem sharedSecretDropHull_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hreg_ext : ∀ pc : BitVec 64, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u hHas hreg_ext htrap_stub
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Trajectory post-hook theorem propagating `hc_codeLoaded : P_sub.CodeLoaded s0.mem`.
    Note (`H1`): `GhostRowReplayOn.replay_at_stub` provides `InvS u` (`P_sub.CodeLoaded u.mem`);
    prefer `sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u` there. -/
theorem sharedSecretDropHull_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {m : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hreg_ext : ∀ pc : BitVec 64, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_fu_sf hrun_u hkf
  rw [← keepOf_sharedSecretDropHullRegion_apply m]
  exact keepLr_false_after_hook_of_outcome
    (sharedSecretDropHull_regionWordsSafe m)
    (sharedSecretDropHullRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ =>
          ⟨f, hf, fun L hL => htf L (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL)⟩)
    (fun L hL => htrap_stub L (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL))
    (sharedSecretDropHullRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((keepOf_sharedSecretDropHullRegion_apply m _).trans hlr_s0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_fu_sf hrun_u hkf

theorem sharedSecretDropHull_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hreg_ext : ∀ pc : BitVec 64, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact sharedSecretDropHull_keepLr_false_after_hook_of_outcome hHas hreg_ext htrap_stub
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem sharedSecretDropHull_lr_trap_at_call_ret
    {P_ghost P_sub : Program} {m : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (htrap_u : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      ∀ pc, keepSharedSecretDropHull m pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepSharedSecretDropHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  rw [← keepOf_sharedSecretDropHullRegion_apply m]
  exact lr_trap_at_call_ret
    (sharedSecretDropHull_regionWordsSafe m)
    (sharedSecretDropHullRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL) pc
        (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hkp))
    hext_u
    (sharedSecretDropHullRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hu_ne_sf
    (fun hr => (keepOf_sharedSecretDropHullRegion_apply m _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

theorem sharedSecretDropHull_lr_trap_at_call
    {P_ghost P_sub : Program} {m : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (htrap_u : keepSharedSecretDropHull m (u.readReg64 .lr) = true →
      TrapHook (u.readReg64 .lr) f_u)
    (hno_ext : ∀ pc, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_u)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  rw [← keepOf_sharedSecretDropHullRegion_apply m]
  exact lr_trap_at_call
    (sharedSecretDropHull_regionWordsSafe m)
    (sharedSecretDropHullRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL))
    (fun pc hkp => hno_ext pc (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hkp))
    hext_u
    (sharedSecretDropHullRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

theorem sharedSecretDropHull_keepLr_false_at_stub_of_outcome
    {P_ghost P_sub : Program} {m stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hreg_ext : ∀ pc : BitVec 64, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : SharedSecretDropEntryGuard m stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  rw [← keepOf_sharedSecretDropHullRegion_apply m]
  exact keepLr_false_at_stub_of_outcome
    (sharedSecretDropHull_regionWordsSafe m)
    (sharedSecretDropHullRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ =>
          ⟨f, hf, fun L hL => htf L (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL)⟩)
    hext_stub
    (fun L hL => htrap_stub L (keepOf_sharedSecretDropHullRegion_apply m _ ▸ hL))
    (sharedSecretDropHullRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((sharedSecretDropEntryGuard_iff_trapEntryGuard m stubPc s0).mp hGuard0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_u_sf hrun_u hpc_u

theorem sharedSecretDropHull_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hreg_ext : ∀ pc : BitVec 64, keepSharedSecretDropHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepSharedSecretDropHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : SharedSecretDropEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact sharedSecretDropHull_keepLr_false_at_stub_of_outcome hHas hreg_ext hext_stub htrap_stub
    hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-! ## 2. Entry-Excluded Adapters & `f3EmptySharedSecretDropGhostHook{,K}` Wrappers -/

/-- Parametric `∀ L` entry-excluded adapter for `keepSharedSecretDropHull m`. -/
theorem sharedSecretDropHull_reg_ext_of_entry_excluded {P_ghost : Program} {m : BitVec 64}
    {entries : List (BitVec 64)}
    (hno_ext_outside : ∀ pc,
      keepSharedSecretDropHull m pc = true → pc ∉ entries → P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries, P_ghost.externAt? e = none ∨
      ∃ f, P_ghost.externAt? e = some f ∧
        ∀ L, keepSharedSecretDropHull m L = true → TrapHook L f) :
    ∀ pc, keepSharedSecretDropHull m pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L, keepSharedSecretDropHull m L = true → TrapHook L f := by
  intro pc hkp
  by_cases hmem : pc ∈ entries
  · exact hentries pc hmem
  · exact Or.inl (hno_ext_outside pc hkp hmem)

/-- Stock/C2 `SharedSecret::drop` specialization (`entries := [m + sharedSecretDropEntryOff]`).
    Only `m + sharedSecretDropEntryOff` (`lsSharedSecretDropSym`) is hooked in `cliHookTablePlaced`;
    `<MontgomeryPoint as Zeroize>::zeroize` at `m` is NOT hooked, so `m` is never excluded and
    `hno_ext_outside` matches STARTUP's `f3Row_ghostProg617_externAt_none_of_ne_entry`. -/
theorem sharedSecretDropHull_reg_ext_of_dropEntry_excluded {P_ghost : Program} {m : BitVec 64}
    {f_stub : State → State}
    (hno_ext_outside : ∀ pc,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) = some f_stub)
    (htrap_stub : ∀ L, keepSharedSecretDropHull m L = true → TrapHook L f_stub) :
    ∀ pc, keepSharedSecretDropHull m pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L, keepSharedSecretDropHull m L = true → TrapHook L f := by
  refine sharedSecretDropHull_reg_ext_of_entry_excluded
    (entries := [m + sharedSecretDropEntryOff])
    (fun pc hkp hmem => hno_ext_outside pc hkp (fun hEq => hmem (List.mem_singleton.mpr hEq))) ?_
  intro e he
  rw [List.mem_singleton.mp he]
  exact Or.inr ⟨f_stub, hext_entry, htrap_stub⟩

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `SharedSecret::drop`
    (`f3EmptySharedSecretDropGhostHook keepR P_sub m`, hooked entry
    `entries = [m + sharedSecretDropEntryOff]`, `keepR` covering all 64 words of
    `keepSharedSecretDropHull m`). -/
theorem f3EmptySharedSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) =
      some (f3EmptySharedSecretDropGhostHook keepR P_sub m))
    {s0 sf : State}
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptySharedSecretDropGhostHook keepR P_sub m u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptySharedSecretDropGhostHook keepR P_sub m u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false :=
  sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u hHas
    (sharedSecretDropHull_reg_ext_of_dropEntry_excluded hno_ext_outside hext_entry
      (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHook_of_cover P_sub hcover hL))
    (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHook_of_cover P_sub hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptySharedSecretDropGhostHook_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) =
      some (f3EmptySharedSecretDropGhostHook keepR P_sub m))
    {s0 sf : State}
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptySharedSecretDropGhostHook keepR P_sub m u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptySharedSecretDropGhostHook keepR P_sub m u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptySharedSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u hHas hcover
    hno_ext_outside hext_entry hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptySharedSecretDropGhostHook_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) =
      some (f3EmptySharedSecretDropGhostHook keepR P_sub m))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : SharedSecretDropEntryGuard m (m + sharedSecretDropEntryOff) s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = m + sharedSecretDropEntryOff →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false :=
  sharedSecretDropHull_keepLr_false_at_stub_of_subroutineOutcome hHas
    (sharedSecretDropHull_reg_ext_of_dropEntry_excluded hno_ext_outside hext_entry
      (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHook_of_cover P_sub hcover hL))
    hext_entry
    (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHook_of_cover P_sub hcover hL)
    hc_codeLoaded hGuard0 hout

theorem f3EmptySharedSecretDropGhostHookK_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) =
      some (f3EmptySharedSecretDropGhostHookK keepR P_sub m))
    {s0 sf : State}
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptySharedSecretDropGhostHookK keepR P_sub m u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptySharedSecretDropGhostHookK keepR P_sub m u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false :=
  sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u hHas
    (sharedSecretDropHull_reg_ext_of_dropEntry_excluded hno_ext_outside hext_entry
      (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHookK_of_cover P_sub hcover hL))
    (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHookK_of_cover P_sub hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptySharedSecretDropGhostHookK_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) =
      some (f3EmptySharedSecretDropGhostHookK keepR P_sub m))
    {s0 sf : State}
    (hlr_s0 : keepSharedSecretDropHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptySharedSecretDropGhostHookK keepR P_sub m u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptySharedSecretDropGhostHookK keepR P_sub m u).mem →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptySharedSecretDropGhostHookK_keepLr_false_after_hook_of_codeLoaded_u hHas hcover
    hno_ext_outside hext_entry hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptySharedSecretDropGhostHookK_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepSharedSecretDropHull m pc = true →
      pc ≠ m + sharedSecretDropEntryOff →
      P_ghost.externAt? pc = none)
    (hext_entry : P_ghost.externAt? (m + sharedSecretDropEntryOff) =
      some (f3EmptySharedSecretDropGhostHookK keepR P_sub m))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : SharedSecretDropEntryGuard m (m + sharedSecretDropEntryOff) s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = m + sharedSecretDropEntryOff →
      keepSharedSecretDropHull m (u.readReg64 .lr) = false :=
  sharedSecretDropHull_keepLr_false_at_stub_of_subroutineOutcome hHas
    (sharedSecretDropHull_reg_ext_of_dropEntry_excluded hno_ext_outside hext_entry
      (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHookK_of_cover P_sub hcover hL))
    hext_entry
    (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHookK_of_cover P_sub hcover hL)
    hc_codeLoaded hGuard0 hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropLrTrap
