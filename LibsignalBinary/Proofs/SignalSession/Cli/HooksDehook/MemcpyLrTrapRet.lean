/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet -- proof-setup: allow-public-import
import ProofLib.OpcodeExclusion
import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# `Returned`-Outcome & Cross-Hook `blk20` Closed-Trap Suite (`HooksDehook.MemcpyLrTrapRet`)

Mirrors `HooksDehook.MemsetLrTrapRet` (`ba4d2cc002`) for `mallocngLib` block 20 (`memcpySymWords`,
`396` B at `mmpl.base 20`) without modifying `HooksDehook/MemcpyLrTrap.lean`:
1. Exposed `@[expose] def Blk20TrapHook` & `@[expose] def Blk20TrapInv` (Pillar 4), plus wrappers
   reusing `MemcpyLrTrap.blk20_lr_trap_false_gen` and `MemcpyLrTrap.blk20_lr_trap_false_subroutineOutcome`.
2. Cross trap-hook lemmas (`rev_c7.md` NIT 4c): `memset` ghost hooks satisfy `Blk20TrapHook L` for
   `L ∈ blk20`, and `memcpy` ghost hooks satisfy `MemsetLrTrapRet.Blk21TrapHook L` for `L ∈ blk21`.
3. `Returned`-case `blk20` traps (`blk20_lr_trap_after_hook_returned` with zero stub premise,
   `blk20_lr_trap_false_mixed_returned` / `_single_returned` / `_memcpy_returned`, and combined
   single-pass `keepMemOps_lr_trap_false_mixed_returned`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memcpySymWords)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (masterMemsetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  keepMemsetBlk21 memsetGhostHook memsetGhostHookK
  memsetGhostHook_of_keepLr_true memsetGhostHookK_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (
  Blk21TrapHook blk21TrapHook_of_exception_on_keepLr blk21_lr_trap_false_mixed_returned
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords
  masterMemcpySpec memcpySpecK memcpySymWords_length
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  keepCoversBlk20_keepMemcpyBlk20 keepMemOps keepMemcpyBlk20
  memcpyGhostHook memcpyGhostHookK
  memcpyGhostHook_of_keepLr_true memcpyGhostHookK_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap (
  blk20_lr_trap_false_gen blk20_lr_trap_false_subroutineOutcome
  mallocngBlockProg20_code_length
)

/-! ## 0. Exposed `Blk20TrapHook` & `Blk20TrapInv` Definitions -/

/-- Hook-level trap preservation at `lr = L`: on any `.Running` state `w` with `w.readReg64 .lr = L`,
    `f w` either transitions to `.Exception _` or stays `.Running` at `pc = L` with `lr = L`. -/
@[expose] def Blk20TrapHook (L : BitVec 64) (f : State → State) : Prop :=
  ∀ w : State, w.status = .Running → w.readReg64 .lr = L →
    (∃ msg, (f w).status = .Exception msg) ∨
    ((f w).status = .Running ∧ (f w).pc = L ∧ (f w).readReg64 .lr = L)

/-- Closed-trap invariant on `blk20` (`396` B at `mmpl.base 20`) with pinned `lr = L`. -/
@[expose] def Blk20TrapInv (mmpl : Obj.MultiPlacement) (L : BitVec 64) (w : State) : Prop :=
  w.status = .Running ∧
  keepMemcpyBlk20 mmpl w.pc = true ∧
  w.readReg64 .lr = L ∧
  (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded w.mem

theorem blk20TrapHook_hookMemcpy (L : BitVec 64) : Blk20TrapHook L hookMemcpy :=
  fun _ hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem blk20TrapHook_hookMemset (L : BitVec 64) : Blk20TrapHook L hookMemset :=
  fun _ hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem blk20TrapHook_memcpyGhostHook {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64) (hkeepL : keep L = true) :
    Blk20TrapHook L (memcpyGhostHook keep P_real P_sub entryTarget) := by
  classical
  intro w hrun hlr
  by_cases hAct : ActiveRealPre masterMemcpySpec w
  · rw [memcpyGhostHook_of_keepLr_true hAct (hlr ▸ hkeepL)]
    exact blk20TrapHook_hookMemcpy L w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    unfold memcpyGhostHook linkedCallHook; simp [hAct]

theorem blk20TrapHook_memcpyGhostHookK {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64) (hkeepL : keep L = true) :
    Blk20TrapHook L (memcpyGhostHookK keep P_real P_sub entryTarget) := by
  intro w _ hlr
  rw [memcpyGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]
  exact Or.inl ⟨"ghost-hook precondition violated", rfl⟩

theorem blk20TrapHook_memcpyGhostHook_of_cover {mmpl : Obj.MultiPlacement} {keep : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemcpyBlk20 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (memcpyGhostHook keep P_real P_sub entryTarget) :=
  fun L hL => blk20TrapHook_memcpyGhostHook P_real P_sub entryTarget (hcover L hL)

/-! ## 1. `(A2)` K-Narrowed `Blk20TrapHook` & Cross Trap-Hook Lemmas (`rev_c7.md` NIT 4c) -/

theorem blk20TrapHook_of_exception_on_keepLr {keep : BitVec 64 → Bool} {L : BitVec 64}
    {f : State → State} (hkeepL : keep L = true)
    (hex_of_keep : ∀ w : State, keep (w.readReg64 .lr) = true →
      ∃ msg, (f w).status = .Exception msg) :
    Blk20TrapHook L f :=
  fun w _ hlr => Or.inl (hex_of_keep w (hlr ▸ hkeepL))

/-- Any `linkedCallHook` whose `spec.pre` implies `keep (w.readReg64 .lr) = false` satisfies
    `Blk20TrapHook L` whenever `keep L = true`. -/
theorem blk20TrapHook_linkedCallHook_of_pre_keepFalse {α : Type}
    {keep keep' : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (spec : Spec α) (fallback : State → State)
    (hpre_lr : ∀ (x : α) (R : SepProp) (w : State),
      (w.mem ⊨ spec.pre x w ∗ R) → keep (w.readReg64 .lr) = false)
    (hkeepL : keep L = true) :
    Blk20TrapHook L (linkedCallHook keep' P_real P_sub entryTarget spec fallback) := by
  refine blk20TrapHook_of_exception_on_keepLr hkeepL fun w hkw => ?_
  classical
  have hnAct : ¬ ActiveRealPre spec w := by
    rintro ⟨_, _, x, R, hpre⟩
    have hfalse := hpre_lr x R w hpre
    rw [hkw] at hfalse
    exact Bool.noConfusion hfalse
  refine ⟨"ghost-hook precondition violated", ?_⟩
  unfold linkedCallHook
  simp [hnAct]

/-- Every `memcpySpecK keep spec`-narrowed `linkedCallHook` with `keep ⊇ keepMemcpyBlk20 mmpl`
    satisfies `∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L (...)`. -/
theorem blk20TrapHook_linkedCallHook_memcpySpecK {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemcpyBlk20 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (spec : Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L
        (linkedCallHook keep' P_real P_sub entryTarget (memcpySpecK keep spec) fallback) := by
  intro L hL
  refine blk20TrapHook_linkedCallHook_of_pre_keepFalse P_real P_sub entryTarget
    (memcpySpecK keep spec) fallback (fun x R w hpre => ?_) (hcover L hL)
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Any `f3LinkedCallHook` whose `(specOf γ tp).pre` implies `keep (w.readReg64 .lr) = false`
    (covering both `h2k_withKeepLrFalse keep` and `h2k_withKeepLrAndFds keep` across all 7 K-route
    ghosts in `h2k_ghFixedK`, as well as `h2k_memsetGhostHookK`) satisfies `Blk20TrapHook L`
    whenever `keep L = true`. -/
theorem blk20TrapHook_f3LinkedCallHook_of_pre_keepFalse {α : Type}
    {keep keep' : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State)
    (hpre_lr : ∀ (γ : GhostName) (tp : BitVec 64) (x : α) (R : SepProp) (w : State),
      (w.mem ⊨ (specOf γ tp).pre x w ∗ R) → keep (w.readReg64 .lr) = false)
    (hkeepL : keep L = true) :
    Blk20TrapHook L (f3LinkedCallHook keep' P_real P_sub entryTarget specOf fallback) := by
  refine blk20TrapHook_of_exception_on_keepLr hkeepL fun w hkw => ?_
  classical
  have hnAct : ¬ ActiveF3CallPre specOf w := by
    rintro ⟨_, _, γ, tp, x, R, hpre⟩
    have hfalse := hpre_lr γ tp x R w hpre
    rw [hkw] at hfalse
    exact Bool.noConfusion hfalse
  refine ⟨"ghost-hook precondition violated", ?_⟩
  unfold f3LinkedCallHook
  simp [hnAct]

/-- Every `memcpySpecK keep`-narrowed `f3LinkedCallHook` (`rfl`-equal to `h2k_withKeepLrFalse keep`)
    with `keep ⊇ keepMemcpyBlk20 mmpl` satisfies
    `∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L (...)`. -/
theorem blk20TrapHook_f3LinkedCallHook_memcpySpecK {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemcpyBlk20 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L
        (f3LinkedCallHook keep' P_real P_sub entryTarget
          (fun γ tp => memcpySpecK keep (specOf γ tp)) fallback) := by
  intro L hL
  refine blk20TrapHook_f3LinkedCallHook_of_pre_keepFalse P_real P_sub entryTarget
    (fun γ tp => memcpySpecK keep (specOf γ tp)) fallback
    (fun γ tp x R w hpre => ?_) (hcover L hL)
  dsimp only [memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Every `(⌜keep (w.readReg64 .lr) = false ∧ P w⌝ ∗ ...)`-narrowed `f3LinkedCallHook` (`rfl`-equal
    to `h2k_withKeepLrAndFds keep` when `P w := FdsGe3Closed w.fs`) with
    `keep ⊇ keepMemcpyBlk20 mmpl` satisfies
    `∀ L, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L (...)`. -/
theorem blk20TrapHook_f3LinkedCallHook_keepAnd {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemcpyBlk20 mmpl a = true → keep a = true)
    (P : State → Prop)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L
        (f3LinkedCallHook keep' P_real P_sub entryTarget
          (fun γ tp =>
            { (specOf γ tp) with
              pre := fun x s =>
                ⌜keep (s.readReg64 .lr) = false ∧ P s⌝ ∗ (specOf γ tp).pre x s })
          fallback) := by
  intro L hL
  refine blk20TrapHook_f3LinkedCallHook_of_pre_keepFalse P_real P_sub entryTarget _ fallback
    (fun γ tp x R w hpre => ?_) (hcover L hL)
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.1

/-- **Cross trap-hook (`memset` → `blk20`):** plain `memsetGhostHook keep P_real P_sub entryTarget`
    satisfies `Blk20TrapHook L` whenever `keep L = true` (e.g. `keep = keepMemOps mmpl` or
    `hole2_keepSub`), via its `hookMemset` fallback / `¬ ActiveRealPre` `.Exception` split. -/
theorem blk20TrapHook_memsetGhostHook
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk20TrapHook L (memsetGhostHook keep P_real P_sub entryTarget) := by
  classical
  intro w hrun hlr
  by_cases hAct : ActiveRealPre masterMemsetSpec w
  · rw [memsetGhostHook_of_keepLr_true hAct (hlr ▸ hkeepL)]
    exact blk20TrapHook_hookMemset L w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    unfold memsetGhostHook linkedCallHook
    simp [hAct]

/-- **Cross trap-hook (`memsetK` → `blk20`):** `K`-narrowed `memsetGhostHookK keep P_real P_sub entryTarget`
    satisfies `Blk20TrapHook L` whenever `keep L = true` via its `.Exception` branch. -/
theorem blk20TrapHook_memsetGhostHookK
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk20TrapHook L (memsetGhostHookK keep P_real P_sub entryTarget) := by
  intro w _ hlr
  rw [memsetGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]
  exact Or.inl ⟨"ghost-hook precondition violated", rfl⟩

theorem blk20TrapHook_memsetGhostHook_of_cover
    {mmpl : Obj.MultiPlacement} {keep : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemcpyBlk20 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (memsetGhostHook keep P_real P_sub entryTarget) :=
  fun L hL => blk20TrapHook_memsetGhostHook P_real P_sub entryTarget (hcover L hL)

theorem blk20TrapHook_memsetGhostHook_keepMemOps
    (mmpl : Obj.MultiPlacement) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (memsetGhostHook (keepMemOps mmpl) P_real P_sub entryTarget) :=
  blk20TrapHook_memsetGhostHook_of_cover
    (fun a ha => by simp [keepMemOps, ha]) P_real P_sub entryTarget

theorem blk20TrapHook_memsetGhostHookK_keepMemOps
    (mmpl : Obj.MultiPlacement) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
      Blk20TrapHook L (memsetGhostHookK (keepMemOps mmpl) P_real P_sub entryTarget) :=
  fun L hL =>
    blk20TrapHook_memsetGhostHookK P_real P_sub entryTarget (by simp [keepMemOps, hL])

/-- **Cross trap-hook (`hookMemcpy` → `blk21`):** `hookMemcpy` satisfies
    `MemsetLrTrapRet.Blk21TrapHook L` for every `L`. -/
theorem blk21TrapHook_hookMemcpy (L : BitVec 64) : Blk21TrapHook L hookMemcpy := by
  intro w hrun hlr
  exact Or.inr ⟨hrun, hlr, hlr⟩

/-- **Cross trap-hook (`memcpy` → `blk21`):** plain `memcpyGhostHook keep P_real P_sub entryTarget`
    satisfies `MemsetLrTrapRet.Blk21TrapHook L` whenever `keep L = true` (e.g. `keep = keepMemOps mmpl`
    or `hole2_keepSub`), via its `hookMemcpy` fallback / `¬ ActiveRealPre` `.Exception` split. -/
theorem blk21TrapHook_memcpyGhostHook
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (memcpyGhostHook keep P_real P_sub entryTarget) := by
  classical
  intro w hrun hlr
  by_cases hAct : ActiveRealPre masterMemcpySpec w
  · rw [memcpyGhostHook_of_keepLr_true hAct (hlr ▸ hkeepL)]
    exact blk21TrapHook_hookMemcpy L w hrun hlr
  · refine Or.inl ⟨"ghost-hook precondition violated", ?_⟩
    unfold memcpyGhostHook linkedCallHook
    simp [hAct]

/-- **Cross trap-hook (`memcpyK` → `blk21`):** `K`-narrowed `memcpyGhostHookK keep P_real P_sub entryTarget`
    satisfies `MemsetLrTrapRet.Blk21TrapHook L` whenever `keep L = true` via its `.Exception` branch. -/
theorem blk21TrapHook_memcpyGhostHookK
    {keep : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keep L = true) :
    Blk21TrapHook L (memcpyGhostHookK keep P_real P_sub entryTarget) := by
  intro w _ hlr
  rw [memcpyGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]
  exact Or.inl ⟨"ghost-hook precondition violated", rfl⟩

theorem blk21TrapHook_memcpyGhostHook_of_cover
    {mmpl : Obj.MultiPlacement} {keep : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (memcpyGhostHook keep P_real P_sub entryTarget) :=
  fun L hL => blk21TrapHook_memcpyGhostHook P_real P_sub entryTarget (hcover L hL)

theorem blk21TrapHook_memcpyGhostHook_keepMemOps
    (mmpl : Obj.MultiPlacement) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (memcpyGhostHook (keepMemOps mmpl) P_real P_sub entryTarget) :=
  blk21TrapHook_memcpyGhostHook_of_cover
    (fun a ha => by simp [keepMemOps, ha]) P_real P_sub entryTarget

theorem blk21TrapHook_memcpyGhostHookK_keepMemOps
    (mmpl : Obj.MultiPlacement) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L (memcpyGhostHookK (keepMemOps mmpl) P_real P_sub entryTarget) :=
  fun L hL =>
    blk21TrapHook_memcpyGhostHookK P_real P_sub entryTarget (by simp [keepMemOps, hL])

theorem blk21TrapHook_linkedCallHook_memcpySpecK {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (spec : Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L
        (linkedCallHook keep' P_real P_sub entryTarget (memcpySpecK keep spec) fallback) := by
  intro L hL
  refine blk21TrapHook_of_exception_on_keepLr (hcover L hL) fun w hkw => ?_
  classical
  have hnAct : ¬ ActiveRealPre (memcpySpecK keep spec) w := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [memcpySpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [hkw] at hpre
    exact Bool.noConfusion hpre.1
  refine ⟨"ghost-hook precondition violated", ?_⟩
  unfold linkedCallHook
  simp [hnAct]

theorem blk21TrapHook_f3LinkedCallHook_memcpySpecK {α : Type}
    {mmpl : Obj.MultiPlacement} {keep keep' : BitVec 64 → Bool}
    (hcover : ∀ a, keepMemsetBlk21 mmpl a = true → keep a = true)
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Spec α) (fallback : State → State) :
    ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true →
      Blk21TrapHook L
        (f3LinkedCallHook keep' P_real P_sub entryTarget
          (fun γ tp => memcpySpecK keep (specOf γ tp)) fallback) := by
  intro L hL
  refine blk21TrapHook_of_exception_on_keepLr (hcover L hL) fun w hkw => ?_
  classical
  have hnAct : ¬ ActiveF3CallPre (fun γ tp => memcpySpecK keep (specOf γ tp)) w := by
    rintro ⟨_, _, γ, tp, x, R, hpre⟩
    dsimp only [memcpySpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [hkw] at hpre
    exact Bool.noConfusion hpre.1
  refine ⟨"ghost-hook precondition violated", ?_⟩
  unfold f3LinkedCallHook
  simp [hnAct]

/-! ## 2. Direct `Returned` Corollaries Reusing `MemcpyLrTrap` (`blk20_lr_trap_false_subroutineOutcome`) -/

/-- Direct `Returned`-outcome wrapper reusing `MemcpyLrTrap.blk20_lr_trap_false_gen` for callers
    already using `MemcpyLrTrap.Blk20TrapHook`. -/
theorem blk20_lr_trap_false_orig_mixed_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
            LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap.Blk20TrapHook L f)
    (hmis : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap.Blk20TrapHook L f)
    {s0 sf : State}
    (hCode0 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_no_mis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_gen hblk20_ext hmis hCode0
    (fun _ => by rw [hpc_sf]; exact hlr_s0)
    (fun _ => by rw [hpc_sf]; exact hlr_no_mis)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- Direct `SubroutineOutcome` wrapper reusing `MemcpyLrTrap.blk20_lr_trap_false_subroutineOutcome`
    verbatim for callers already using `MemcpyLrTrap.Blk20TrapHook`. -/
theorem blk20_lr_trap_false_orig_subroutineOutcome {α : Type} {spec : Spec α}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
            LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap.Blk20TrapHook L f)
    (hmis : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true →
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrap.Blk20TrapHook L f)
    {x : α} {R : SepProp} {s0 sf : State}
    (hCode0 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_no_mis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr))
    (hout : SubroutineOutcome spec x R s0 sf) :
    ∀ u : State, Steps P_ghost s0 u → Steps P_ghost u sf → u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_subroutineOutcome hblk20_ext hmis hCode0 hlr_s0 hlr_no_mis hout

/-! ## 3. `(A1)` + `(A2)` Closed-Trap Impossibility & `Returned` Suite on Exposed `Blk20TrapHook` -/

private def isBlk20SafeInstr (off : Nat) (inst : Instr) : Bool :=
  match inst with
  | .ret rn => decide (rn = .lr)
  | .nop => decide (off + 4 < 396)
  | .bCond _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .cbz _ _ _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .tbz _ _ _ _ relOff =>
    decide (off + 4 < 396) && decide ((BitVec.ofNat 64 off + relOff).toNat < 396)
  | .addSubImm _ _ rd _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .addSubShift _ _ rd _ _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .logicalImm _ _ rd _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .bitfield _ _ rd _ _ _ =>
    decide (off + 4 < 396) && decide (rd ≠ .lr)
  | .ldr _ _ _ rt addr =>
    decide (off + 4 < 396) && decide (rt ≠ .lr) && decide (addr.baseReg ≠ .lr)
  | .str _ _ addr =>
    decide (off + 4 < 396) && decide (addr.baseReg ≠ .lr)
  | .ldp _ _ rt1 rt2 addr =>
    decide (off + 4 < 396) && decide (rt1 ≠ .lr) && decide (rt2 ≠ .lr) &&
      decide (addr.baseReg ≠ .lr)
  | .stp _ _ _ addr =>
    decide (off + 4 < 396) && decide (addr.baseReg ≠ .lr)
  | _ => false

private theorem memcpyWords_all_safe :
    ((List.range 99).all fun k =>
      match memcpySymWords[k]? with
      | some w =>
        match decode w with
        | some inst => isBlk20SafeInstr (4 * k) inst
        | none => false
      | none => false) = true := by
  decide +kernel

private theorem isBlk20SafeInstr_not_isSvc0 {off : Nat} {inst : Instr}
    (h : isBlk20SafeInstr off inst = true) :
    inst.isSvc0 = false := by
  cases inst <;> simp [isBlk20SafeInstr, Instr.isSvc0] at h ⊢

private def Blk20StepOutcome (base : BitVec 64) (s s' : State) : Prop :=
  (∃ msg, s'.status = .Exception msg) ∨
  (s'.status = .Running ∧
   s'.readReg64 .lr = s.readReg64 .lr ∧
   (s'.pc = s.readReg64 .lr ∨ ∃ off' : Nat, off' < 396 ∧ s'.pc = base + BitVec.ofNat 64 off'))

private def SameRunLrPc (s s1 : State) : Prop :=
  s1.status = s.status ∧ s1.readReg64 .lr = s.readReg64 .lr ∧ s1.pc = s.pc

private theorem readReg64_lr_writeReg64_ne (s : State) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    (s.writeReg64 r v).readReg64 .lr = s.readReg64 .lr := by
  cases r with
  | gpr idx =>
    unfold State.writeReg64 State.readReg64 RegFile.read RegFile.write
    have hne : 30#5 ≠ idx := fun h => hr (by subst h; rfl)
    by_cases h31 : idx == 31#5
    · simp [h31]
    · simp [h31, hne]
  | sp => rfl
  | xzr => rfl

private theorem sameRunLrPc_refl (s : State) : SameRunLrPc s s := ⟨rfl, rfl, rfl⟩

private theorem sameRunLrPc_writeReg64 {s s1 : State} (h : SameRunLrPc s s1)
    {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    SameRunLrPc s (s1.writeReg64 r v) :=
  ⟨h.1, (readReg64_lr_writeReg64_ne s1 hr v).trans h.2.1, h.2.2⟩

private theorem sameRunLrPc_writeReg {s s1 : State} (h : SameRunLrPc s s1)
    (w : Width) {r : Reg} (hr : r ≠ .lr) (v : BitVec 64) :
    SameRunLrPc s (s1.writeReg w r v) :=
  sameRunLrPc_writeReg64 h hr _

private theorem sameRunLrPc_setPState {s s1 : State} (h : SameRunLrPc s s1) (ps : PState) :
    SameRunLrPc s (s1.setPState ps) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_optPState {s s1 : State} (h : SameRunLrPc s s1)
    (optPs : Option PState) :
    SameRunLrPc s (match optPs with | some ps => s1.setPState ps | none => s1) := by
  cases optPs with
  | none => exact h
  | some ps => exact sameRunLrPc_setPState h ps

private theorem sameRunLrPc_setMem {s s1 : State} (h : SameRunLrPc s s1) (m : Memory) :
    SameRunLrPc s (s1.setMem m) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem sameRunLrPc_addrWb {s s1 : State} (s0 : State) (h : SameRunLrPc s s1)
    {addr : AddrMode} (hbr : addr.baseReg ≠ .lr) :
    SameRunLrPc s (match (evalAddrMode s0 addr).2 with
      | some (base, newBase) => s1.writeReg64 base newBase
      | none => s1) := by
  cases addr <;> dsimp only [evalAddrMode, AddrMode.baseReg] at hbr ⊢
  · exact h
  · exact h
  · exact sameRunLrPc_writeReg64 h hbr _
  · exact sameRunLrPc_writeReg64 h hbr _
  · exact h

private theorem outcome_of_advancePC {base : BitVec 64} {off : Nat} {s s1 : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (hoff : off + 4 < 396)
    (h1 : SameRunLrPc s s1) :
    Blk20StepOutcome base s s1.advancePC := by
  refine Or.inr ⟨h1.1.trans hrun, h1.2.1, Or.inr ⟨off + 4, hoff, ?_⟩⟩
  change s1.pc + 4#64 = base + BitVec.ofNat 64 (off + 4)
  rw [h1.2.2, hpc, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem outcome_of_branchRel {base : BitVec 64} {off : Nat} {relOff : BitVec 64} {s : State}
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off)
    (htgt : (BitVec.ofNat 64 off + relOff).toNat < 396) :
    Blk20StepOutcome base s (s.setPC (s.pc + relOff)) := by
  refine Or.inr ⟨hrun, rfl, Or.inr ⟨(BitVec.ofNat 64 off + relOff).toNat, htgt, ?_⟩⟩
  change s.pc + relOff = base + BitVec.ofNat 64 (BitVec.ofNat 64 off + relOff).toNat
  rw [hpc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h
  exact ⟨rfl, rfl⟩

private theorem blk20_ite {base : BitVec 64} {s : State} {c : Prop} [inst : Decidable c]
    {t e : State} (ht : Blk20StepOutcome base s t) (he : Blk20StepOutcome base s e) :
    Blk20StepOutcome base s (if c then t else e) :=
  match inst with
  | isTrue _ => ht
  | isFalse _ => he

private theorem execInst_of_isBlk20SafeInstr
    {base : BitVec 64} {off : Nat} {inst : Instr} {s : State}
    (hsafe : isBlk20SafeInstr off inst = true)
    (hrun : s.status = .Running)
    (hpc : s.pc = base + BitVec.ofNat 64 off) :
    Blk20StepOutcome base s (execInst inst s) := by
  cases inst <;> try (unfold isBlk20SafeInstr at hsafe; contradiction)
  case ret rn =>
    unfold isBlk20SafeInstr at hsafe
    have hrn : rn = .lr := of_decide_eq_true hsafe
    subst hrn
    exact Or.inr ⟨hrun, rfl, Or.inl rfl⟩
  case nop =>
    unfold isBlk20SafeInstr at hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hsafe) (sameRunLrPc_refl s)
  case bCond cond relOff =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change Blk20StepOutcome base s
      (if ConditionHolds cond s.pstate then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case cbz w isNonZero rt relOff =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    let val := s.readReg w rt
    let c := if isNonZero then (val == 0#64) != true else val == 0#64
    change Blk20StepOutcome base s (if c then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case tbz w isNonZero rt bit relOff =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, htgt0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have htgt := of_decide_eq_true htgt0
    change Blk20StepOutcome base s
      (if (s.readReg64 rt).getLsbD bit == isNonZero then s.setPC (s.pc + relOff) else s.advancePC)
    split
    · exact outcome_of_branchRel hrun hpc htgt
    · exact outcome_of_advancePC hrun hpc hoff (sameRunLrPc_refl s)
  case addSubImm w op rd rn imm12 shift12 =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case addSubShift w op rd rn rm shift amount =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case logicalImm w op rd rn mask =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_optPState
        (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _) _)
  case bitfield w op rd rn immr imms =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hrd0⟩ := band_true hsafe
    exact outcome_of_advancePC hrun hpc (of_decide_eq_true hoff0)
      (sameRunLrPc_writeReg (sameRunLrPc_refl s) w (of_decide_eq_true hrd0) _)
  case ldr w sz signed rt addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨h12, hbr0⟩ := band_true hsafe
    obtain ⟨hoff0, hrt0⟩ := band_true h12
    have hoff := of_decide_eq_true hoff0
    have hrt := of_decide_eq_true hrt0
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execLdr w sz signed rt addr s)
    unfold execLdr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_writeReg (sameRunLrPc_addrWb s (sameRunLrPc_refl s) hbr) w hrt _)
  case str sz rt addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execStr sz rt addr s)
    unfold execStr
    split
    · exact Or.inl ⟨_, rfl⟩
    · dsimp only []
      split
      · exact Or.inl ⟨_, rfl⟩
      · exact outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)
  case ldp w signed rt1 rt2 addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨h123, hbr0⟩ := band_true hsafe
    obtain ⟨h12, hrt20⟩ := band_true h123
    obtain ⟨hoff0, hrt10⟩ := band_true h12
    have hoff := of_decide_eq_true hoff0
    have hrt1 := of_decide_eq_true hrt10
    have hrt2 := of_decide_eq_true hrt20
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execLdp w signed rt1 rt2 addr s)
    unfold execLdp
    exact blk20_ite (Or.inl ⟨_, rfl⟩)
      (blk20_ite (Or.inl ⟨_, rfl⟩)
        (outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_writeReg
            (sameRunLrPc_writeReg (sameRunLrPc_addrWb s (sameRunLrPc_refl s) hbr) _ hrt1 _)
            _ hrt2 _)))
  case stp w rt1 rt2 addr =>
    unfold isBlk20SafeInstr at hsafe
    obtain ⟨hoff0, hbr0⟩ := band_true hsafe
    have hoff := of_decide_eq_true hoff0
    have hbr := of_decide_eq_true hbr0
    change Blk20StepOutcome base s (execStp w rt1 rt2 addr s)
    unfold execStp
    exact blk20_ite (Or.inl ⟨_, rfl⟩)
      (blk20_ite (Or.inl ⟨_, rfl⟩)
        (outcome_of_advancePC hrun hpc hoff
          (sameRunLrPc_addrWb s (sameRunLrPc_setMem (sameRunLrPc_refl s) _) hbr)))

private theorem fetchMem_blk20_safe
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {m : Memory}
    {pc : BitVec 64} {inst : Instr}
    (hkeep : keepMemcpyBlk20 mmpl pc = true)
    (hL : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hfm : P_ghost.fetchMem m pc = some inst) :
    ∃ off : Nat, off < 396 ∧
      pc = mmpl.base 20 + BitVec.ofNat 64 off ∧
      isBlk20SafeInstr off inst = true := by
  have hoff_lt : (pc - mmpl.base 20).toNat < 396 := of_decide_eq_true hkeep
  let off := (pc - mmpl.base 20).toNat
  have hpc_eq : pc = mmpl.base 20 + BitVec.ofNat 64 off := by
    dsimp only [off]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm (mmpl.base 20),
      BitVec.sub_add_cancel]
  have hfm0 := hfm
  unfold Program.fetchMem at hfm0
  cases heg : P_ghost.externAt? pc with
  | some _ => simp [heg] at hfm0
  | none =>
    simp only [heg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm0
    split at hfm0
    · contradiction
    rename_i hal_neg
    have hal : pc.toNat % 4 = 0 := Classical.not_not.mp hal_neg
    have hbase_al : (mmpl.base 20).toNat % 4 = 0 := hL.aligned
    have hnowrap : (mmpl.base 20).toNat + 396 ≤ 2 ^ 64 := by
      have hnw := hL.no_wrap
      rwa [mallocngBlockProg20_code_length mmpl] at hnw
    have hpc_nat : pc.toNat = (mmpl.base 20).toNat + off := by
      rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hoff_mod : off % 4 = 0 := by omega
    let k := off / 4
    have hoff_k : off = 4 * k := by omega
    have hk : k < 99 := by omega
    have hk_len : k < memcpySymWords.length := by rw [memcpySymWords_length]; exact hk
    have hall_k := List.all_eq_true.mp memcpyWords_all_safe k (List.mem_range.mpr hk)
    rw [List.getElem?_eq_getElem hk_len] at hall_k
    dsimp only [] at hall_k
    cases hdec : decode memcpySymWords[k] with
    | none =>
      rw [hdec] at hall_k
      contradiction
    | some inst' =>
      rw [hdec] at hall_k
      dsimp only [] at hall_k
      let P_sub := mallocngBlockProg mmpl 20 Syscall.standard
      have hrw := (mallocngBlockProg20_hasWords mmpl Syscall.standard).2.1 k hk_len
      change P_sub.readWordOff ((mmpl.base 20 - mmpl.base 20).toNat + 4 * k) =
        some memcpySymWords[k] at hrw
      rw [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, ← hoff_k] at hrw
      have hext_sub : P_sub.externAt? pc = none :=
        mallocngBlockProg20_externAt_none mmpl Syscall.standard pc
      have hfetch_sub : P_sub.fetch pc = some inst' := by
        unfold Program.fetch
        have hbase_sub : (pc - P_sub.base).toNat = off := rfl
        rw [hext_sub, hbase_sub, hrw]
        exact hdec
      have hfm_sub : P_sub.fetchMem m pc = some inst' := P_sub.fetchMem_of_fetch hL hfetch_sub
      have hfm_eq : P_ghost.fetchMem m pc = P_sub.fetchMem m pc :=
        ProofLib.Variant.fetchMem_eq_of_externAt_eq (heg.trans hext_sub.symm)
      rw [hfm_eq, hfm_sub] at hfm
      cases hfm
      exact ⟨off, hoff_lt, hpc_eq, hoff_k ▸ hall_k⟩

/-- **`(A1)` Generalized closed-trap impossibility (`blk20_trap_impossible_ret`):**
    No `Steps P_ghost w sf` starting in `Blk20TrapInv mmpl L w` (`keepMemcpyBlk20 mmpl L = true`)
    can reach `sf` satisfying `sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false`,
    `∀ msg, sf.status ≠ .Exception msg`, and `sf.status ≠ .Halted`. -/
theorem blk20_trap_impossible_ret
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {L : BitVec 64}
    (hL_in : keepMemcpyBlk20 mmpl L = true)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk20TrapHook L f)
    {w sf : State}
    (hsteps : Steps P_ghost w sf)
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hInv : Blk20TrapInv mmpl L w) :
    False := by
  induction hsteps with
  | refl _ =>
    have hfalse := hrun_sf' hInv.1
    rw [hInv.2.1] at hfalse
    exact Bool.noConfusion hfalse
  | @step s1 s2 s3 h1 hrest ih =>
    rcases hInv with ⟨hrun1, hkeep1, hlr1, hCode1⟩
    have hCode2 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s2.mem :=
      h1.codeLoaded hCode1
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      have hst : s3.status = .Halted := by rw [heq]
      exact hnhalt_sf hst
    | extern_fault _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      have hst : s3.status = .Exception "extern hook modified read-only memory or symbol table" := by
        rw [heq]
      exact hnoex_sf _ hst
    | @extern f _ hext _ _ =>
      rcases hblk20_ext s1.pc hkeep1 with hnone | ⟨f', hext', htrap⟩
      · rw [hnone] at hext; contradiction
      · rw [hext'] at hext
        injection hext with hfeq
        subst hfeq
        rcases htrap s1 hrun1 hlr1 with ⟨msg, hex⟩ | ⟨hrun2, hpc2, hlr2⟩
        · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
            (by rw [hex]; nofun)
          have hst : s3.status = .Exception msg := by rw [heq, hex]
          exact hnoex_sf msg hst
        · exact ih hrun_sf' hnoex_sf hnhalt_sf ⟨hrun2, hpc2 ▸ hL_in, hlr2, hCode2⟩
    | @exec inst _ hfm =>
      obtain ⟨off, _, hpc1, hsafe⟩ := fetchMem_blk20_safe hkeep1 hCode1 hfm
      have hnsvc0 := isBlk20SafeInstr_not_isSvc0 hsafe
      have heval : P_ghost.evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
      rcases execInst_of_isBlk20SafeInstr hsafe hrun1 hpc1 with
        ⟨msg, hex⟩ | ⟨hrun2, hlr_eq, hpc_next⟩
      · have hex' : (P_ghost.evalInst inst s1).status = .Exception msg := heval ▸ hex
        have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
          (by rw [hex']; nofun)
        have hst : s3.status = .Exception msg := by rw [heq, hex']
        exact hnoex_sf msg hst
      · rw [heval] at ih hCode2
        have hkeep2 : keepMemcpyBlk20 mmpl (execInst inst s1).pc = true := by
          rcases hpc_next with hpc_ret | ⟨off', hoff', hpc_off⟩
          · rw [hpc_ret, hlr1]; exact hL_in
          · rw [hpc_off]; exact keepCoversBlk20_keepMemcpyBlk20 mmpl off' hoff'
        exact ih hrun_sf' hnoex_sf hnhalt_sf ⟨hrun2, hkeep2, hlr_eq.trans hlr1, hCode2⟩

/-- **Post-hook continuation `lr = false` (`blk20_lr_trap_after_hook_ret`, `(A1)` + `(A2)`):**
    Given the post-hook continuation `hrest : Steps P_ghost (f_u u) sf` (the exact continuation
    provided in `GhostExternReplaysOn`), requires **only** `hrun_sf'`, `hnoex_sf`, and `hnhalt_sf`
    on `sf` (zero stub inequality `sf.pc ≠ stubPc` needed). -/
theorem blk20_lr_trap_after_hook_ret
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_u : State → State}
    {u sf : State}
    (htrap_u : ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f_u)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hCode_fu : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  cases hkeepL : keepMemcpyBlk20 mmpl (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    let L := u.readReg64 .lr
    have hblk20_L : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
        P_ghost.externAt? pc = none ∨ ∃ f, P_ghost.externAt? pc = some f ∧ Blk20TrapHook L f := by
      intro pc hkp
      rcases hblk20_ext pc hkp with hnone | ⟨f, hf, htf⟩
      · exact Or.inl hnone
      · exact Or.inr ⟨f, hf, htf L hkeepL⟩
    rcases htrap_u L hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
    · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest
        (by rw [hex]; nofun)
      have hst : sf.status = .Exception msg := by rw [heq, hex]
      exact hnoex_sf msg hst
    · exact blk20_trap_impossible_ret hkeepL hblk20_L hrest hrun_sf' hnoex_sf hnhalt_sf
        ⟨hrun_v, hpc_v ▸ hkeepL, hlr_v, hCode_fu⟩

/-- **Post-hook `Returned`-case `blk20` trap (`blk20_lr_trap_after_hook_returned`):**
    On `Steps P_ghost (f_u u) sf` with `sf.status = .Running` and `sf.pc = s0.readReg64 .lr`,
    requires **only** `keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false` (no stub fact needed!). -/
theorem blk20_lr_trap_after_hook_returned
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_u : State → State}
    {s0 u sf : State}
    (htrap_u : ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f_u)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hCode_fu : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false) :
    keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_after_hook_ret htrap_u hblk20_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- **Call-point `lr = false` on `Steps P_ghost u sf` (`blk20_lr_trap_at_call_ret`):**
    At `u = sf` (`Steps.refl`), `sf` has not executed `f_u`, so `hu_ne_sf` rules out stopping right
    on the unexecuted ghost stub `u.pc` while `.Running`. -/
theorem blk20_lr_trap_at_call_ret
    {P_ghost : Program} {mmpl : Obj.MultiPlacement} {f_u : State → State}
    {u sf : State}
    (htrap_u : ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f_u)
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  cases hsteps_u_sf with
  | refl =>
    exact False.elim (hu_ne_sf hrun_u rfl)
  | @step _ v _ h1 hrest =>
    have hCode_v : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded v.mem :=
      h1.codeLoaded hCode_u
    cases h1 with
    | exec _ hfm =>
      unfold Program.fetchMem at hfm
      rw [hext_u] at hfm
      contradiction
    | halt_unmapped _ _ hext0 =>
      rw [hext_u] at hext0; contradiction
    | extern_fault _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      have hst : sf.status =
          .Exception "extern hook modified read-only memory or symbol table" := by rw [heq]
      exact False.elim (hnoex_sf _ hst)
    | @extern f _ hext _ _ =>
      rw [hext_u] at hext
      injection hext with hfeq
      subst hfeq
      exact blk20_lr_trap_after_hook_ret htrap_u hblk20_ext hCode_v hrest
        hrun_u hrun_sf' hnoex_sf hnhalt_sf

/-- **`(A1)` + `(A2)` Global `hlr_calls` Theorem (`blk20_lr_trap_false_ret`):**
    Mirror of `MemsetLrTrapRet.blk21_lr_trap_false_ret` on exposed `Blk20TrapHook`. -/
theorem blk20_lr_trap_false_ret
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hret_no_mis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hmis
  obtain ⟨f_u, hext_u, htrap_u⟩ := hmis_trap u.pc hmis
  exact blk20_lr_trap_at_call_ret htrap_u hblk20_ext hext_u
    (hsteps_s0_u.codeLoaded hc_codeLoaded)
    hsteps_u_sf hrun_u
    (fun hrun_sf heq_pc => hmis (heq_pc ▸ hret_no_mis hrun_sf))
    hrun_sf' hnoex_sf hnhalt_sf

/-- `SubroutineOutcome` specialization of `blk20_lr_trap_false_ret` on exposed `Blk20TrapHook`. -/
theorem blk20_lr_trap_false_subroutineOutcome_ret {α : Type} {spec : Spec α}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {x : α} {R : SepProp} {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_no_mis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr))
    (hout : SubroutineOutcome spec x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false := by
  have hrun_sf' : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false := by
    intro hrun
    rcases hout with ⟨⟨hpc, _, _⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hpc]; exact hlr_s0
    · rw [hpan] at hrun; cases hrun
    · rw [hex] at hrun; cases hrun
    · rw [hoom] at hrun; cases hrun
  have hret_no_mis : sf.status = .Running → P_ghost.externAt? sf.pc = P_real.externAt? sf.pc := by
    intro hrun
    rcases hout with ⟨⟨hpc, _, _⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hpc]; exact hlr_no_mis
    · rw [hpan] at hrun; cases hrun
    · rw [hex] at hrun; cases hrun
    · rw [hoom] at hrun; cases hrun
  have hnoex_sf : ∀ msg, sf.status ≠ .Exception msg := by
    intro msg hex0
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hex0] at hr; cases hr
    · rw [hex0] at hpan; cases hpan
    · rw [hex0] at hex; cases hex
    · rw [hex0] at hoom; cases hoom
  have hnhalt_sf : sf.status ≠ .Halted := by
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hpan, _⟩ | ⟨_, hex, _⟩ | ⟨hoom, _⟩
    · rw [hr]; nofun
    · rw [hpan]; nofun
    · rw [hex]; nofun
    · rw [hoom]; nofun
  exact blk20_lr_trap_false_ret hblk20_ext hmis_trap hc_codeLoaded
    hrun_sf' hret_no_mis hnoex_sf hnhalt_sf

/-- Non-`.Running` specialization of `blk20_lr_trap_false_ret` (covers `.Exited _`, `.Panicked`,
    `.OutOfMemory`, and `.Signaled _`). -/
theorem blk20_lr_trap_false_mixed_nonRunning
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_ret hblk20_ext hmis_trap hc_codeLoaded
    (fun hr => False.elim (hrun_sf hr))
    (fun hr => False.elim (hrun_sf hr))
    hnoex_sf hnhalt_sf

/-- **Mixed-pass `(A2)` `Returned`-outcome specialization (`blk20_lr_trap_false_mixed_returned`):**
    Mirror of `MemsetLrTrapRet.blk21_lr_trap_false_mixed_returned`: when `sf.status = .Running` at
    `sf.pc = s0.readReg64 .lr` with `keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false` and no extern
    mismatch at `s0.readReg64 .lr`, every mismatched call along `s0 →* u →* sf` has
    `keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false`. -/
theorem blk20_lr_trap_false_mixed_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_trap : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_no_mis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_ret hblk20_ext hmis_trap hc_codeLoaded
    (fun _ => by rw [hpc_sf]; exact hlr_s0)
    (fun _ => by rw [hpc_sf]; exact hlr_no_mis)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- Single-stub `Returned`-outcome specialization (`blk20_lr_trap_false_single_returned`). -/
theorem blk20_lr_trap_false_single_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_stub : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_ne_stub : s0.readReg64 .lr ≠ stubPc) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_mixed_returned hblk20_ext
    (fun pc hmis => ⟨f_stub, hmis_stub pc hmis ▸ hext_stub, htrap_stub⟩)
    hc_codeLoaded hrun_sf hpc_sf hlr_s0
    (Classical.byContradiction fun hne => hlr_ne_stub (hmis_stub _ hne))

/-- `memcpyGhostHook` `Returned`-outcome specialization (`blk20_lr_trap_false_memcpy_returned`):
    discharges `Blk20TrapHook` automatically for
    `memcpyGhostHook (keepMemcpyBlk20 mmpl) P_hookReal P_sub entryTarget`. -/
theorem blk20_lr_trap_false_memcpy_returned
    {P_ghost P_real P_hookReal P_sub : Program} {mmpl : Obj.MultiPlacement}
    {stubPc entryTarget : BitVec 64}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hmis_stub : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc → pc = stubPc)
    (hext_stub : P_ghost.externAt? stubPc =
      some (memcpyGhostHook (keepMemcpyBlk20 mmpl) P_hookReal P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false)
    (hlr_ne_stub : s0.readReg64 .lr ≠ stubPc) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
  blk20_lr_trap_false_single_returned hblk20_ext hmis_stub hext_stub
    (fun _ hL => blk20TrapHook_memcpyGhostHook P_hookReal P_sub entryTarget hL)
    hc_codeLoaded hrun_sf hpc_sf hlr_s0 hlr_ne_stub

/-- **Combined single-pass `memset` + `memcpy` `Returned`-outcome theorem
    (`keepMemOps_lr_trap_false_mixed_returned`):**
    Pairs `blk20_lr_trap_false_mixed_returned` and `blk21_lr_trap_false_mixed_returned` so that a
    single pass de-hooking `memset`, `memcpy`, and any K-route ghosts simultaneously obtains
    `keepMemOps mmpl (u.readReg64 .lr) = false` (`keepMemcpyBlk20 = false` ∧
    `keepMemsetBlk21 = false`) at every mismatched call along `s0 →* u →* sf`. -/
theorem keepMemOps_lr_trap_false_mixed_returned
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement}
    (hblk20_ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hmis_both : ∀ pc, P_ghost.externAt? pc ≠ P_real.externAt? pc →
      ∃ f, P_ghost.externAt? pc = some f ∧
        (∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f) ∧
        (∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f))
    {s0 sf : State}
    (hc20 : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s0.mem)
    (hc21 : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s0.mem)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepMemOps mmpl (s0.readReg64 .lr) = false)
    (hlr_no_mis : P_ghost.externAt? (s0.readReg64 .lr) = P_real.externAt? (s0.readReg64 .lr)) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keepMemOps mmpl (u.readReg64 .lr) = false := by
  have hlr20_s0 : keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false := by
    unfold keepMemOps at hlr_s0
    exact (Bool.or_eq_false_iff.mp hlr_s0).1
  have hlr21_s0 : keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false := by
    unfold keepMemOps at hlr_s0
    exact (Bool.or_eq_false_iff.mp hlr_s0).2
  intro u hs1 hs2 hrun_u hmis
  have h20 : keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
    blk20_lr_trap_false_mixed_returned hblk20_ext
      (fun pc hm => let ⟨f, hf, ht20, _⟩ := hmis_both pc hm; ⟨f, hf, ht20⟩)
      hc20 hrun_sf hpc_sf hlr20_s0 hlr_no_mis u hs1 hs2 hrun_u hmis
  have h21 : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
    blk21_lr_trap_false_mixed_returned hblk21_ext
      (fun pc hm => let ⟨f, hf, _, ht21⟩ := hmis_both pc hm; ⟨f, hf, ht21⟩)
      hc21 hrun_sf hpc_sf hlr21_s0 hlr_no_mis u hs1 hs2 hrun_u hmis
  unfold keepMemOps
  rw [h20, h21]
  rfl

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet
