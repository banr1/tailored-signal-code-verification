/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Placed.Multi
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common

/-!
# Shared `.rodata` image-fact and `Spec` simulation combinators

Defines `RoDataAt` (`m.RO addr bytes.length ∧ m.readBytes addr bytes.length = bytes`), its pure
and separating `Spec` wrappers (`withRoData`, `withRoDataSep`), and the forward-simulation relation
`SpecSimulates` for transporting `subroutine_ok` and `MultiPlacedLib.subroutineOk` across specs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.Common

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)

/-- Pure read-only image-byte fact: `[addr, addr + bytes.length)` is mapped read-only (`Perm.ro`,
    not `lazyFree`) and holds `bytes` in `m`. -/
def RoDataAt (m : Memory) (addr : BitVec 64) (bytes : List (BitVec 8)) : Prop :=
  m.RO addr bytes.length ∧ m.readBytes addr bytes.length = bytes

/-- Adjoin the pure read-only `.rodata` image fact `⌜RoDataAt s0.mem addr bytes⌝` to `spec.pre`,
    preserving `spec`'s spatial footprint while supplying `(addr ↦ᵣ bytes)` via
    `Satisfies.rodata_intro`. -/
def withRoData {α : Type} (addr : BitVec 64) (bytes : List (BitVec 8)) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜RoDataAt s0.mem addr bytes⌝ ∗ spec.pre x s0 }

/-- Frame `(addr ↦ᵣ bytes)` explicitly in `spec.pre` and `spec.post`. -/
def withRoDataSep {α : Type} (addr : BitVec 64) (bytes : List (BitVec 8)) (spec : Spec α) :
    Spec α :=
  { spec with
    pre := fun x s0 => (addr ↦ᵣ bytes) ∗ spec.pre x s0
    post := fun x s0 sf => (addr ↦ᵣ bytes) ∗ spec.post x s0 sf }

theorem keepsFs_withRoData {α : Type} (addr : BitVec 64) (bytes : List (BitVec 8))
    (spec : Spec α) :
    keepsFs (withRoData addr bytes spec) = withRoData addr bytes (keepsFs spec) := rfl

/-- Relational forward-simulation witness from `spec₁` to `spec₂`: any entry state satisfying
    `spec₂.pre y s0 ∗ R` instantiates a ghost `x` and callee frame `R₁` satisfying
    `spec₁.pre x s0 ∗ R₁` whose `SubroutineOutcome` implies `SubroutineOutcome spec₂ y R s0 sf`. -/
def SpecSimulates {α β : Type} (spec₁ : Spec α) (spec₂ : Spec β) : Prop :=
  ∀ (y : β) (R : SepProp) (s0 : State),
    (s0.mem ⊨ spec₂.pre y s0 ∗ R) →
    ∃ (x : α) (R₁ : SepProp),
      (s0.mem ⊨ spec₁.pre x s0 ∗ R₁) ∧
      ∀ sf, SubroutineOutcome spec₁ x R₁ s0 sf → SubroutineOutcome spec₂ y R s0 sf

theorem SpecSimulates.trans {α β γ : Type} {spec₁ : Spec α} {spec₂ : Spec β} {spec₃ : Spec γ}
    (h₁₂ : SpecSimulates spec₁ spec₂) (h₂₃ : SpecSimulates spec₂ spec₃) :
    SpecSimulates spec₁ spec₃ := by
  intro z R s0 hpre₃
  obtain ⟨y, R₂, hpre₂, hm₂⟩ := h₂₃ z R s0 hpre₃
  obtain ⟨x, R₁, hpre₁, hm₁⟩ := h₁₂ y R₂ s0 hpre₂
  exact ⟨x, R₁, hpre₁, fun sf hout => hm₂ sf (hm₁ sf hout)⟩

/-- Construct `SpecSimulates spec₁ spec₂` for a non-panicking, non-exiting, non-OOM `spec₁`
    from normal-return pre/post transport alone. -/
theorem SpecSimulates.of_map {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec₂.pre y s0 ∗ R) →
      ∃ (x : α) (R₁ : SepProp),
        (s0.mem ⊨ spec₁.pre x s0 ∗ R₁) ∧
        ∀ sf, Returned s0 sf → CallingConventionPreserved s0 sf →
          (sf.mem ⊨ spec₁.post x s0 sf ∗ R₁) →
          (sf.mem ⊨ spec₂.post y s0 sf ∗ R))
    (hpan : spec₁.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec₁.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec₁.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates spec₁ spec₂ := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hpost⟩ := hmap y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · exact Or.inl ⟨hret, hcc, hpost sf hret hcc hp⟩
  · rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [hex] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [hoom] at hp; exact False.elim (not_satisfies_false_sepConj hp)

/-- Transport `subroutine_ok` along `SpecSimulates`. -/
theorem SpecSimulates.subroutine_ok {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {prog : Program} {entry : BitVec 64}
    (h : Arm64.subroutine_ok prog entry spec₁) :
    Arm64.subroutine_ok prog entry spec₂ := by
  apply subroutine_ok.of_codeLoaded
  intro y R s0 hpc hrun hpre hsp _hL
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  exact h.mono_outcome x R₁ s0 hpc hrun hpre₁ hsp hm

/-- Lift `SpecSimulates` across `MultiPlacedLib.withCodeLoaded`. -/
theorem SpecSimulates.withCodeLoaded {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) (lib : MultiPlacedLib) (mpl : MultiPlacement) :
    SpecSimulates (lib.withCodeLoaded mpl spec₁) (lib.withCodeLoaded mpl spec₂) := by
  intro y R s0 hpre
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre ⊢
  rw [sepConj_comm (spec₂.pre y s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_comm (spec₁.pre x s0) ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl]
  exact hpre₁

/-- Lift a placement-indexed `SpecSimulates` family across `MultiPlacedLib.subroutineOk`. -/
theorem SpecSimulates.multiSubroutineOk {α β : Type} {lib : MultiPlacedLib}
    {fnName : String} {spec₁ : MultiPlacement → Spec α}
    {spec₂ : MultiPlacement → Spec β}
    {externs overrides : String → Option (State → State)}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (h : lib.subroutineOk fnName spec₁ externs overrides) :
    lib.subroutineOk fnName spec₂ externs overrides := by
  obtain ⟨hexp, i, off, hfn, hsub⟩ := h
  exact ⟨hexp, i, off, hfn, fun mpl hpl =>
    ((hsim mpl).withCodeLoaded lib mpl).subroutine_ok (hsub mpl hpl)⟩

/-- Drop `keepsFs` along `SpecSimulates` (preserving `onPanic`, `onExit`, and `onOom`). -/
theorem SpecSimulates.drop_keepsFs {α : Type} {spec : Spec α} :
    SpecSimulates (keepsFs spec) spec := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | hout
  · dsimp only [keepsFs] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact Or.inl ⟨hret, hcc, hp.2⟩
  · exact Or.inr hout

/-- Lower `withRoDataSep addr bytes spec` to `withRoData addr bytes spec` along `SpecSimulates`
    (for `bytes.length ≤ 2 ^ 64`). -/
theorem SpecSimulates.withRoData_of_sep {α : Type} {addr : BitVec 64}
    {bytes : List (BitVec 8)} {spec : Spec α} (hlen : bytes.length ≤ 2 ^ 64) :
    SpecSimulates (withRoDataSep addr bytes spec) (withRoData addr bytes spec) := by
  intro x R s0 hpre
  dsimp only [withRoData, withRoDataSep] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hro, hread⟩, hpre⟩ := hpre
  refine ⟨x, R, ?_, fun sf hout => ?_⟩
  · rw [sepConj_assoc]
    exact Satisfies.rodata_intro hro hread hlen hpre
  · rcases hout with ⟨hret, hcc, hpost⟩ | hout
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only at hpost ⊢
      rw [sepConj_assoc] at hpost
      exact Satisfies.of_sep_right hpost
    · exact Or.inr hout

/-- Commute `withRoDataSep addr bytes (keepsFs spec)` to `keepsFs (withRoDataSep addr bytes spec)`. -/
theorem SpecSimulates.keepsFs_withRoDataSep {α : Type} {addr : BitVec 64}
    {bytes : List (BitVec 8)} {spec : Spec α} :
    SpecSimulates (withRoDataSep addr bytes (keepsFs spec))
      (keepsFs (withRoDataSep addr bytes spec)) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoDataSep, keepsFs] at hpost ⊢
    rw [sepConj_left_comm (addr ↦ᵣ bytes) ⌜sf.fs = s0.fs⌝] at hpost
    exact hpost
  · exact Or.inr hout

/-- Drop `keepsFs` inside `withRoDataSep addr bytes (keepsFs spec)`. -/
theorem SpecSimulates.drop_keepsFs_withRoDataSep {α : Type} {addr : BitVec 64}
    {bytes : List (BitVec 8)} {spec : Spec α} :
    SpecSimulates (withRoDataSep addr bytes (keepsFs spec))
      (withRoDataSep addr bytes spec) :=
  SpecSimulates.keepsFs_withRoDataSep.trans SpecSimulates.drop_keepsFs

/-- Any non-panicking, non-exiting, non-OOM `subroutine_ok` for `withRoDataSep addr bytes spec`
    lowers to `withRoData addr bytes spec` (for `bytes.length ≤ 2 ^ 64`) via
    `Satisfies.rodata_intro` and `Satisfies.of_sep_right`. -/
theorem subroutine_ok_withRoData_of_sep {α : Type} {prog : Program} {entry : BitVec 64}
    {addr : BitVec 64} {bytes : List (BitVec 8)} {spec : Spec α}
    (hlen : bytes.length ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withRoDataSep addr bytes spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry (withRoData addr bytes spec) := by
  have _ : _ ∧ _ ∧ _ := ⟨hpan, hex, hoom⟩
  exact (SpecSimulates.withRoData_of_sep hlen).subroutine_ok h

end LibsignalBinary.Proofs.HookDischarge.RustStd.Common
