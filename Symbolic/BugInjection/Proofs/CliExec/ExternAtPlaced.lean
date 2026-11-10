/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced

/-!
# Placed Hook-Tree Agreement

Proves `PrebuildSpecPlaced.HooksAgreePlaced` for `overlayHooksPlaced W (stubsOfMpl mpl) .empty`
against `(Placed.cliProgPlacedSig mpl mmpl W).externAt?` by characterizing `Program.externAt?` at
block `617` of `libsignalSessionLib` and matching first-hit lookup across `block617Externs`.

Because `HooksAgreePlaced` unfolds to a `∀` over a `match` on `btGet progPlacedDepth (overlayHooksPlaced ...)`,
callers should apply these theorems with `@` so elaboration does not reduce `overlayHooksPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.ExternAtPlaced

open Arm64 (Program State)
open Arm64.Obj (MultiPlacedLib MultiPlacement PlacedLib)
open CryptoVerification.SignalSession (CliHooks cliExternsPlacedSig libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree btGet btGet_empty)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (hasCliHookPlaced)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound (hasCliHookPlaced_eq_isSome)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (overlayHooksPlaced progPlacedDepth
  progPlacedWordBound)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound (btGet_overlayHooksPlaced
  hookStubPlacedAt?)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (block617Externs block617Externs_eq
  checkHooksAlignedPlaced checkHooksAlignedPlacedW extractImageHooksPlaced resolve_block617Extern
  stubsOfMpl)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced (HooksAgreePlaced)

private theorem option_or_none {α : Type} (o : Option α) : o.or none = o := by
  cases o <;> rfl

private theorem findSome?_if_none {α β : Type} (p : α → Bool) :
    ∀ (xs : List α),
      (xs.findSome? fun x => if p x then (none : Option β) else none) = none
  | [] => rfl
  | x :: rest => by
    rw [List.findSome?_cons]
    cases p x <;> exact findSome?_if_none p rest

private theorem findSome?_map_eq {α β γ : Type} (f : α → β) (g : β → Option γ) :
    ∀ (xs : List α), (xs.map f).findSome? g = xs.findSome? fun x => g (f x)
  | [] => rfl
  | x :: rest => by
    simp only [List.map_cons, List.findSome?_cons]
    cases g (f x) <;> [exact findSome?_map_eq f g rest; rfl]

private theorem findSome?_congr_mem {α β : Type} {xs : List α} {f g : α → Option β}
    (hfg : ∀ x ∈ xs, f x = g x) :
    xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.findSome?_cons]
    rw [hfg x (.head rest), ih (fun y hy => hfg y (.tail x hy))]

private theorem sub_toNat_beq_eq (a b base : BitVec 64) :
    ((a - base).toNat == (b - base).toNat) = (a.toNat == b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have ha := a.isLt
    have hb := b.isLt
    have hc := base.isLt
    rw [BitVec.toNat_sub, BitVec.toNat_sub] at h
    omega
  · intro h
    have hab : a = b := BitVec.eq_of_toNat_eq h
    subst hab
    rfl

/-- `Program.externAt?` of `lib.blockProgram mpl i X` depends only on
`(lib.blocks.getD i { code := [] }).externs`, `lib.resolve mpl`, and `mpl.base i`. -/
theorem blockProgram_externAt? (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat)
    (X : String → Option (State → State)) (pc : BitVec 64) :
    (lib.blockProgram mpl i X).externAt? pc =
      (lib.blocks.getD i { code := [] }).externs.findSome? fun e =>
        if (lib.resolve mpl e - mpl.base i).toNat == (pc - mpl.base i).toNat then X e else none := by
  unfold MultiPlacedLib.blockProgram PlacedLib.program MultiPlacedLib.blockLib
    MultiPlacedLib.blockPlacement Program.externAt? Program.hookAtOff?
  dsimp only
  rw [findSome?_if_none, option_or_none, findSome?_map_eq]

/-- Characterization of `(cliProgPlacedSig mpl mmpl W).externAt? pc` via `block617Externs` and `mpl.ρ`. -/
theorem cliProgPlacedSig_externAt? (mpl mmpl : MultiPlacement) (W : CliHooks) (pc : BitVec 64) :
    (cliProgPlacedSig mpl mmpl W).externAt? pc =
      block617Externs.findSome? fun e =>
        if (mpl.ρ e).toNat == pc.toNat then cliExternsPlacedSig mmpl W e else none := by
  unfold cliProgPlacedSig
  rw [blockProgram_externAt?, block617Externs_eq]
  apply findSome?_congr_mem
  intro e he
  rw [resolve_block617Extern he mpl, sub_toNat_beq_eq]

/-- Lookup in `overlayHooksPlaced W (stubsOfMpl mpl) .empty` at any 4-byte-aligned `pc : BitVec 64`. -/
theorem btGet_overlayHooksPlaced_stubsOfMpl (mpl : MultiPlacement) (W : CliHooks)
    {pc : BitVec 64} (hmod4 : pc.toNat % 4 = 0) :
    btGet progPlacedDepth (overlayHooksPlaced W (stubsOfMpl mpl) .empty) (pc.toNat / 4) =
      block617Externs.findSome? fun e =>
        if (mpl.ρ e).toNat == pc.toNat then
          if hasCliHookPlaced W e then some e else none
        else none := by
  have hpc_lt : pc.toNat < 2 ^ 64 := pc.isLt
  have hwb : progPlacedWordBound = 2 ^ 62 := rfl
  have hidx : pc.toNat / 4 < progPlacedWordBound := by rw [hwb]; omega
  have hmul : 4 * (pc.toNat / 4) = pc.toNat := by omega
  have hbt := btGet_overlayHooksPlaced W (stubsOfMpl mpl) .empty hidx
  rw [btGet_empty, hmul] at hbt
  rw [hbt]
  have hstub : hookStubPlacedAt? W (stubsOfMpl mpl) pc.toNat =
      block617Externs.findSome? fun e =>
        if (mpl.ρ e).toNat == pc.toNat then
          if hasCliHookPlaced W e then some e else none
        else none := by
    unfold hookStubPlacedAt? stubsOfMpl
    exact findSome?_map_eq (fun e => (e, (mpl.ρ e).toNat))
      (fun (n, va) => if va == pc.toNat then (if hasCliHookPlaced W n then some n else none) else none)
      block617Externs
  rw [hstub]
  cases (block617Externs.findSome? fun e =>
    if (mpl.ρ e).toNat == pc.toNat then
      if hasCliHookPlaced W e then some e else none
    else none) <;> rfl

/-- First-match `some name` agreement over `es`: by `hasCliHookPlaced_eq_isSome`, any aliased stub `e`
at `va` satisfies `hasCliHookPlaced W e = true` iff `cliExternsPlacedSig mmpl W e` is `some`. -/
private theorem findSome?_hookStub_some {mpl mmpl : MultiPlacement} {W : CliHooks}
    {va : Nat} {name : String} {h : State → State} :
    ∀ {es : List String},
      (es.findSome? fun e =>
          if (mpl.ρ e).toNat == va then
            if hasCliHookPlaced W e then some e else none
          else none) = some name →
      cliExternsPlacedSig mmpl W name = some h →
      (es.findSome? fun e =>
        if (mpl.ρ e).toNat == va then cliExternsPlacedSig mmpl W e else none) = some h
  | [], hstub, _ => nomatch hstub
  | e :: rest, hstub, hext => by
    rw [List.findSome?_cons] at hstub ⊢
    cases hva : ((mpl.ρ e).toNat == va)
    · simp only [hva, Bool.false_eq_true, ↓reduceIte] at hstub ⊢
      exact findSome?_hookStub_some hstub hext
    · simp only [hva, ↓reduceIte, hasCliHookPlaced_eq_isSome mmpl W e] at hstub ⊢
      cases he : cliExternsPlacedSig mmpl W e with
      | none =>
        simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hstub ⊢
        exact findSome?_hookStub_some hstub hext
      | some h0 =>
        simp only [he, Option.isSome_some, ↓reduceIte] at hstub ⊢
        injection hstub with hnm
        subst hnm
        rw [he] at hext
        exact hext

private theorem findSome?_hookStub_none {mpl mmpl : MultiPlacement} {W : CliHooks}
    {va : Nat} :
    ∀ {es : List String},
      (es.findSome? fun e =>
          if (mpl.ρ e).toNat == va then
            if hasCliHookPlaced W e then some e else none
          else none) = none →
      (es.findSome? fun e =>
        if (mpl.ρ e).toNat == va then cliExternsPlacedSig mmpl W e else none) = none
  | [], _ => rfl
  | e :: rest, hstub => by
    rw [List.findSome?_cons] at hstub ⊢
    cases hva : ((mpl.ρ e).toNat == va)
    · simp only [hva, Bool.false_eq_true, ↓reduceIte] at hstub ⊢
      exact findSome?_hookStub_none hstub
    · simp only [hva, ↓reduceIte, hasCliHookPlaced_eq_isSome mmpl W e] at hstub ⊢
      cases he : cliExternsPlacedSig mmpl W e with
      | none =>
        simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hstub ⊢
        exact findSome?_hookStub_none hstub
      | some h0 =>
        simp only [he, Option.isSome_some, ↓reduceIte] at hstub
        nomatch hstub

/-- Unconditional `HooksAgreePlaced` for `overlayHooksPlaced W (stubsOfMpl mpl) .empty` across all
`mpl`, `mmpl`, and `W`. -/
theorem hooksAgreePlaced_stubsOfMpl_unconditional (mpl mmpl : MultiPlacement) (W : CliHooks) :
    HooksAgreePlaced mpl mmpl W (overlayHooksPlaced W (stubsOfMpl mpl) .empty) := by
  unfold HooksAgreePlaced
  intro pc hmod4
  cases hbt : btGet progPlacedDepth (overlayHooksPlaced W (stubsOfMpl mpl) .empty) (pc.toNat / 4) with
  | some name =>
    intro h hext
    rw [btGet_overlayHooksPlaced_stubsOfMpl mpl W hmod4] at hbt
    rw [cliProgPlacedSig_externAt? mpl mmpl W pc]
    exact findSome?_hookStub_some hbt hext
  | none =>
    rw [btGet_overlayHooksPlaced_stubsOfMpl mpl W hmod4] at hbt
    rw [cliProgPlacedSig_externAt? mpl mmpl W pc]
    exact findSome?_hookStub_none hbt

theorem hooksAgreePlacedW_stubsOfMpl {mpl mmpl : MultiPlacement} {W : CliHooks}
    (_halign : checkHooksAlignedPlacedW W mpl = true) :
    HooksAgreePlaced mpl mmpl W (overlayHooksPlaced W (stubsOfMpl mpl) .empty) :=
  @hooksAgreePlaced_stubsOfMpl_unconditional mpl mmpl W

theorem hooksAgreePlaced_stubsOfMpl {mpl mmpl : MultiPlacement}
    (_halign : checkHooksAlignedPlaced mpl = true) :
    HooksAgreePlaced mpl mmpl compHooks0
      (overlayHooksPlaced compHooks0 (stubsOfMpl mpl) .empty) :=
  @hooksAgreePlaced_stubsOfMpl_unconditional mpl mmpl compHooks0

theorem hooksAgreePlaced_extractImageHooksPlaced (mpl mmpl : MultiPlacement) :
    HooksAgreePlaced mpl mmpl compHooks0 (extractImageHooksPlaced mpl) :=
  @Eq.ndrec (BinTree String)
    (overlayHooksPlaced compHooks0 (stubsOfMpl mpl) .empty)
    (fun t => HooksAgreePlaced mpl mmpl compHooks0 t)
    (@hooksAgreePlaced_stubsOfMpl_unconditional mpl mmpl compHooks0)
    (extractImageHooksPlaced mpl)
    rfl

end Symbolic.BugInjection.Proofs.CliExec.ExternAtPlaced
