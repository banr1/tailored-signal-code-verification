/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.Musl.Proofs.CryptoHooks
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs

/-!
# Shared combinators and CLI spec mirrors for `libc` hook discharge

Provides `ProcessFieldsPreserved` projections (`fs_eq`, `trace_eq`), lightweight CLI contract
wrappers (`keepsFs`, `withStack`, `bytesAt`, `cStrAt`), and generic `subroutine_ok` framing
combinators (`subroutine_ok_inImage`, `subroutine_ok_withStack`, `subroutine_ok_withStack_keepsFs`,
`subroutine_ok_drop_keepsFs`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Libc.Common

open Arm64 ProofLib
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)

/-- Adjoins `⌜sf.fs = s0.fs⌝` to `spec`'s normal-return postcondition. -/
def keepsFs {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜sf.fs = s0.fs⌝ ∗ spec.post x s0 sf }

/-- Frames `stackAt s.sp hookStack` in `pre` and `stackAt s0.sp hookStack` in `post`. -/
def withStack {α : Type} (spec : Spec α) (hookStack : Nat := extHookStack) : Spec α :=
  { spec with
    pre := fun x s => spec.pre x s ∗ stackAt s.sp hookStack
    post := fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp hookStack }

/-- Read-only (`↦ᵣ`) byte slice when `ro = true`, read-write (`↦ₛ`) when `ro = false`. -/
def bytesAt (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then p ↦ᵣ bs else p ↦ₛ bs

/-- NUL-terminated read-write byte slice `p ↦ₛ (s ++ [0#8])`. -/
def cStrAt (p : BitVec 64) (s : List (BitVec 8)) : SepProp :=
  p ↦ₛ (s ++ [0#8])

theorem keepsFs_inImage {α : Type} (spec : Spec α) (img : Obj.Image) :
    (keepsFs spec).inImage img = keepsFs (spec.inImage img) := rfl

theorem ProcessFieldsPreserved.fs_eq {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    sf.fs = s0.fs := h.1

theorem ProcessFieldsPreserved.trace_eq {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    sf.trace = s0.trace := h.2.1

/-- Any `subroutine_ok prog entry spec` weakens to `(spec.inImage img)`. -/
theorem subroutine_ok_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp (fun _ hout => hout)

/-- Any `subroutine_ok prog entry (keepsFs spec)` weakens to `subroutine_ok prog entry spec`. -/
theorem subroutine_ok_drop_keepsFs {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry (keepsFs spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok_map h
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
    (fun x R' s0 sf _ hp => by dsimp only [keepsFs] at hp; rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by dsimp only [keepsFs] at he; rw [hex] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by dsimp only [keepsFs] at ho; rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [keepsFs] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-- Frame `stackAt s0.sp hookStack` around any non-panicking, non-exiting, non-OOM `subroutine_ok`. -/
theorem subroutine_ok_withStack {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hookStack : Nat)
    (h : subroutine_ok prog entry spec)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry (withStack spec hookStack) := by
  refine subroutine_ok_map h
    (fun x R s0 hpre => ?_)
    (fun x R' s0 sf _ hp => by rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by rw [hex] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [withStack] at hpre
  rw [sepConj_assoc] at hpre
  refine ⟨x, stackAt s0.sp hookStack ∗ R, hpre, fun sf hpost => ?_⟩
  dsimp only [withStack]
  rwa [sepConj_assoc]

/-- Commute `withStack` inside `keepsFs` on `subroutine_ok`. -/
theorem subroutine_ok_withStack_keepsFs {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hookStack : Nat)
    (h : subroutine_ok prog entry (keepsFs spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry (keepsFs (withStack spec hookStack)) := by
  have hw := subroutine_ok_withStack hookStack h
    (by dsimp [keepsFs]; exact hpan)
    (by dsimp [keepsFs]; exact hex)
    (by dsimp [keepsFs]; exact hoom)
  refine subroutine_ok_map hw
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
    (fun x R' s0 sf _ hp => by dsimp only [withStack, keepsFs] at hp; rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by dsimp only [withStack, keepsFs] at he; rw [hex] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by dsimp only [withStack, keepsFs] at ho; rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [withStack, keepsFs] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, Satisfies.of_eq hpost.2⟩

/-- Weaken `s0.mem ⊨ bytesAt ro p bs ∗ R` to `s0.mem ⊨ (p ↦ᵣ bs) ∗ R`. -/
theorem satisfies_bytesAt_to_ro {m : Memory} {ro : Bool} {p : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ bytesAt ro p bs ∗ R) :
    m ⊨ (p ↦ᵣ bs) ∗ R := by
  cases ro
  · exact Satisfies.pointsToBytes_to_ro h
  · exact h

end LibsignalBinary.Proofs.HookDischarge.Libc.Common
