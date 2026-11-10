/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

/-!
# Hook-Free `subroutine_ok` Stack-Framing Lift and `Spec.inOptImage`

Provides general combinators for lifting `subroutine_ok` contracts across `.inImage` invariants and
larger stack budgets without re-stepping instructions:
- `subroutine_ok_inImage_of_subroutine_ok` and `subroutine_ok_inOptImage_of_subroutine_ok`: lift
  `subroutine_ok P addr spec` to `spec.inImage img` / `spec.inOptImage oimg`.
- `subroutine_ok_frame_entails` and `subroutine_ok_inImage_of_frame_entails`: frame an arbitrary
  assertion `Frame x s0` across normal return, panic, exit, and OOM outcomes.
- `subroutine_ok_of_stack_split` and `subroutine_ok_inImage_of_stack_split`: lift hook-free
  contracts from `stackAt s0.sp s1` to `stackAt s0.sp s2` (`s1 ≤ s2 ≤ 2 ^ 64`) via
  `stackAt_eq_top_sep_bottom`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.InImageLift

open Arm64 ProofLib SepProp

/-- Unifies plain `Spec α` (`none`) and `Spec.inImage spec img` (`some img`) definitionally. -/
@[simp] def _root_.Arm64.Spec.inOptImage {α : Type} (spec : Spec α) : Option Obj.Image → Spec α
  | none     => spec
  | some img => spec.inImage img

/-- Optional frozen-image + symbol-table invariant matching `Spec.inOptImage`. -/
@[simp] def OptCallInv : Option Obj.Image → State → Prop
  | none,     _ => True
  | some img, s => img.FrozenLoaded s ∧ s.symtab = img.symtab

theorem OptCallInv.of_steps {P : Program} {oimg : Option Obj.Image} {s s' : State}
    (hinv : OptCallInv oimg s) (hsteps : Steps P s s') : OptCallInv oimg s' := by
  cases oimg with
  | none => trivial
  | some img => exact ⟨hsteps.frozenLoaded hinv.1, hsteps.symtab_eq.trans hinv.2⟩

/-- Any `subroutine_ok P addr spec` entails `subroutine_ok P addr (spec.inImage img)`. -/
theorem subroutine_ok_inImage_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal fun _ hout => hout

/-- Any `subroutine_ok P addr spec` entails `subroutine_ok P addr (spec.inOptImage oimg)`. -/
theorem subroutine_ok_inOptImage_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (oimg : Option Obj.Image) (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (spec.inOptImage oimg) := by
  cases oimg with
  | none => exact h
  | some img => exact subroutine_ok_inImage_of_subroutine_ok img h

/-- Frame an extra assertion `Frame x s0` across `subroutine_ok P addr specSmall` to establish
`subroutine_ok P addr specBig` (handling normal return, panic, exit, and OOM uniformly). -/
theorem subroutine_ok_frame_entails {α : Type} {P : Program} {addr : BitVec 64}
    {specSmall specBig : Spec α} (Frame : α → State → SepProp)
    (h : subroutine_ok P addr specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢ specSmall.pre x s0 ∗ Frame x s0)
    (hpost : ∀ x s0 sf, specSmall.post x s0 sf ∗ Frame x s0 ⊢ specBig.post x s0 sf)
    (hpan : ∀ x s0 sf, specSmall.onPanic x s0 sf ∗ Frame x s0 ⊢ specBig.onPanic x s0 sf := by
      intro _ _ _; exact Entails.trans (Entails.of_eq (by simp [sepConj])) (by exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)))
    (hex : ∀ x code s0 sf, specSmall.onExit x code s0 sf ∗ Frame x s0 ⊢ specBig.onExit x code s0 sf := by
      intro _ _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hoom : ∀ x s0 sf, specSmall.onOom x s0 sf ∗ Frame x s0 ⊢ specBig.onOom x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)) :
    subroutine_ok P addr specBig := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hm hal => ?_
  have hm' : s0.mem ⊨ specSmall.pre x s0 ∗ (Frame x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hm
  refine h.mono_outcome x (Frame x s0 ∗ R) s0 hpc hrun hm' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hp⟩ | ⟨ho_st, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hp
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hp
  · refine Or.inr (Or.inr (Or.inl ⟨code, hex_st, ?_⟩))
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hex x code s0 sf)) hp
  · refine Or.inr (Or.inr (Or.inr ⟨ho_st, ?_⟩))
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hoom x s0 sf)) hp

/-- Lift `subroutine_ok P addr specSmall` directly to `subroutine_ok P addr (specBig.inImage img)`
by framing `Frame x s0`. -/
theorem subroutine_ok_inImage_of_frame_entails {α : Type} {P : Program} {addr : BitVec 64}
    {specSmall specBig : Spec α} (img : Obj.Image) (Frame : α → State → SepProp)
    (h : subroutine_ok P addr specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢ specSmall.pre x s0 ∗ Frame x s0)
    (hpost : ∀ x s0 sf, specSmall.post x s0 sf ∗ Frame x s0 ⊢ specBig.post x s0 sf)
    (hpan : ∀ x s0 sf, specSmall.onPanic x s0 sf ∗ Frame x s0 ⊢ specBig.onPanic x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hex : ∀ x code s0 sf, specSmall.onExit x code s0 sf ∗ Frame x s0 ⊢ specBig.onExit x code s0 sf := by
      intro _ _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hoom : ∀ x s0 sf, specSmall.onOom x s0 sf ∗ Frame x s0 ⊢ specBig.onOom x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)) :
    subroutine_ok P addr (specBig.inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_frame_entails Frame h hpre hpost hpan hex hoom)

/-- Split `stackAt sp s2` (`s1 ≤ s2 ≤ 2 ^ 64`) into `stackAt sp s1 ∗ memRegion (sp - s2) (s2 - s1)`
for convenient framing of hook-free `subroutine_ok` proofs from `4096 + frame` to `16384 + frame`. -/
theorem stackAt_eq_top_sep_bottom (sp : BitVec 64) {s1 s2 : Nat}
    (hle : s1 ≤ s2 := by decide) (hbound : s2 ≤ 2 ^ 64 := by decide) :
    stackAt sp s2 = stackAt sp s1 ∗ memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) := by
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have h0 := ProofLib.stackAt_split_bottom sp s1 (s2 - s1) (by omega)
  rw [← hsplit] at h0
  exact h0.trans (by ac_rfl)

/-- Lift a hook-free `subroutine_ok` contract from stack footprint `s1` to `s2` (`s1 ≤ s2 ≤ 2 ^ 64`)
by framing the bottom `s2 - s1` stack bytes. -/
theorem subroutine_ok_of_stack_split {α : Type} {P : Program} {addr : BitVec 64}
    {specSmall specBig : Spec α} (s1 s2 : Nat)
    (h : subroutine_ok P addr specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢
      specSmall.pre x s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1))
    (hpost : ∀ x s0 sf,
      specSmall.post x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.post x s0 sf)
    (hpan : ∀ x s0 sf,
      specSmall.onPanic x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onPanic x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hex : ∀ x code s0 sf,
      specSmall.onExit x code s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onExit x code s0 sf := by
      intro _ _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hoom : ∀ x s0 sf,
      specSmall.onOom x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onOom x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)) :
    subroutine_ok P addr specBig :=
  subroutine_ok_frame_entails
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1))
    h hpre hpost hpan hex hoom

theorem subroutine_ok_inImage_of_stack_split {α : Type} {P : Program} {addr : BitVec 64}
    {specSmall specBig : Spec α} (img : Obj.Image) (s1 s2 : Nat)
    (h : subroutine_ok P addr specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢
      specSmall.pre x s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1))
    (hpost : ∀ x s0 sf,
      specSmall.post x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.post x s0 sf)
    (hpan : ∀ x s0 sf,
      specSmall.onPanic x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onPanic x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hex : ∀ x code s0 sf,
      specSmall.onExit x code s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onExit x code s0 sf := by
      intro _ _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hoom : ∀ x s0 sf,
      specSmall.onOom x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onOom x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)) :
    subroutine_ok P addr (specBig.inImage img) :=
  subroutine_ok_inImage_of_frame_entails img
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1))
    h hpre hpost hpan hex hoom

end CryptoVerification.InImageLift
