/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
import Arm64.Trusted.Spec.SepLogic

/-!
# AArch64 Rust ABI Combinators

`Arm64.Spec` combinators (`Spec.rustPair`, `Spec.rustOption64`, `Spec.rustOption8`,
`Spec.rustResult64`, `Spec.rustNiche64`, `Spec.rustSret`, `Spec.rustSliceFn1`) and `.intro`,
`.mono`, and `.apply` rules for `extern "Rust"` calling conventions on AArch64.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Combinators -/

/-- `Arm64.Spec` for a Rust subroutine of two 64-bit arguments in `(X0, X1)` returning a 2×64-bit
    `ScalarPair` in `(X0, X1)` related to the arguments by `P`. -/
@[simp, arm64_norm]
def _root_.Arm64.Spec.rustPair (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop) :
    Spec (BitVec 64 × BitVec 64) where
  pre  := fun a s0 => ⌜s0.readReg64 Reg.x0 = a.1 ∧ s0.readReg64 Reg.x1 = a.2⌝
  post := fun a _ sf => ⌜P a.1 a.2 (sf.readReg64 Reg.x0) (sf.readReg64 Reg.x1)⌝

/-- `Arm64.Spec` for a Rust subroutine of two 64-bit arguments in `(X0, X1)` returning an
    `Option<u64>` (`ScalarPair` with 32-bit discriminant in `W0` and 64-bit payload in `X1`). -/
@[simp, arm64_norm]
def _root_.Arm64.Spec.rustOption64 (P : BitVec 64 → BitVec 64 → BitVec 32 → BitVec 64 → Prop) :
    Spec (BitVec 64 × BitVec 64) where
  pre  := fun a s0 => ⌜s0.readReg64 Reg.x0 = a.1 ∧ s0.readReg64 Reg.x1 = a.2⌝
  post := fun a _ sf => ⌜P a.1 a.2 (sf.readReg32 Reg.x0) (sf.readReg64 Reg.x1)⌝

/-- `Arm64.Spec` for a Rust subroutine of one 32-bit argument in `W0` returning an `Option<u8>`
    (`ScalarPair` with discriminant in `W0` and 8-bit payload in `W1[7:0]`). -/
@[simp, arm64_norm]
def _root_.Arm64.Spec.rustOption8 (P : BitVec 32 → BitVec 32 → BitVec 8 → Prop) :
    Spec (BitVec 32) where
  pre  := fun c s0 => ⌜s0.readReg32 Reg.x0 = c⌝
  post := fun c _ sf => ⌜P c (sf.readReg32 Reg.x0) ((sf.readReg32 Reg.x1).truncate 8)⌝

/-- `Arm64.Spec` for a Rust subroutine returning a 2×64-bit `Result<u64, u64>` in `(X0, X1)`. -/
@[simp, arm64_norm]
abbrev _root_.Arm64.Spec.rustResult64 (P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop) :
    Spec (BitVec 64 × BitVec 64) :=
  Spec.rustPair P

/-- `Arm64.Spec` for a Rust subroutine returning a niche-optimized `Option<NonZeroU64>` in `X0`
    (`0` = `None`, non-zero `v` = `Some v`). -/
@[simp, arm64_norm]
def _root_.Arm64.Spec.rustNiche64 (P : BitVec 64 → Option (BitVec 64) → Prop) : Spec (BitVec 64) where
  pre  := fun a s0 => ⌜s0.readReg64 Reg.x0 = a⌝
  post := fun a _ sf => ⌜P a (decodeNiche64 (sf.readReg64 Reg.x0))⌝

/-- `Arm64.Spec` for a Rust subroutine taking a pointer/scalar argument in `X0` and an indirect
    result pointer (`sret`) in `X8`. -/
@[simp, arm64_norm]
def _root_.Arm64.Spec.rustSret {α : Type}
    (preRegs : α → BitVec 64 → BitVec 64 → State → Prop)
    (preMem : α → BitVec 64 → BitVec 64 → SepProp)
    (postRegs : α → BitVec 64 → BitVec 64 → State → State → Prop)
    (postMem : α → BitVec 64 → BitVec 64 → SepProp) :
    Spec (α × BitVec 64 × BitVec 64) :=
  Spec.split
    (fun (x, arg, sret) s0 =>
      s0.readReg64 Reg.x0 = arg ∧
      s0.readReg64 Reg.x8 = sret ∧
      preRegs x arg sret s0)
    (fun (x, arg, sret) => preMem x arg sret)
    (fun (x, arg, sret) s0 sf => postRegs x arg sret s0 sf)
    (fun (x, arg, sret) => postMem x arg sret)

/-- `Arm64.Spec` for a read-only Rust subroutine taking a byte slice `&[u8]` (`(ptr, len)` in
    `(X0, X1)` with `ptr ↦ₛ bs` preserved) and returning `f bs : BitVec 64` in `X0`. -/
@[simp, arm64_norm, wp_norm]
abbrev _root_.Arm64.Spec.rustSliceFn1 (f : List (BitVec 8) → BitVec 64) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre  := fun (ptr, bs) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length⌝ ∗ (ptr ↦ₛ bs)
  post := fun (ptr, bs) _ sf =>
    ⌜sf.readReg64 .x0 = f bs⌝ ∗ (ptr ↦ₛ bs)

/-! ## `ScalarPair` return rules -/

theorem _root_.Arm64.Spec.rustPair.intro {prog : Program} {entry : BitVec 64}
    {P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop}
    (h : ∀ (a : BitVec 64 × BitVec 64) (R : SepProp) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      ((s0.readReg64 Reg.x0 = a.1 ∧ s0.readReg64 Reg.x1 = a.2) ∧ (s0.mem ⊨ R)) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0
        (SubroutinePost (Spec.rustPair P) a R s0)) :
    subroutine_ok prog entry (Spec.rustPair P) :=
  subroutine_ok_intro fun a R s0 hpc hrun hpre hsp =>
    reaches_pc_mono (h a R s0 hpc hrun (by simpa using hpre) hsp)
      (fun _ _ _ hp => hp) (fun _ _ ho => False.elim ho)

theorem _root_.Arm64.Spec.rustPair.mono {prog : Program} {entry : BitVec 64}
    {P Q : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop}
    (h : subroutine_ok prog entry (Spec.rustPair P))
    (himp : ∀ a b r0 r1, P a b r0 r1 → Q a b r0 r1) :
    subroutine_ok prog entry (Spec.rustPair Q) :=
  subroutine_ok_mono_entails h (fun _ _ => Entails.refl _)
    (fun a _ sf => Entails.pure_mono (himp a.1 a.2 (sf.readReg64 Reg.x0) (sf.readReg64 Reg.x1)))

theorem _root_.Arm64.Spec.rustPair.apply {prog : Program} {entry : BitVec 64}
    {P : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop}
    (h : subroutine_ok prog entry (Spec.rustPair P)) {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0
      (fun sf => P (s0.readReg64 Reg.x0) (s0.readReg64 Reg.x1) (sf.readReg64 Reg.x0) (sf.readReg64 Reg.x1)) :=
  reaches_pc_mono
    (subroutine_ok_apply h (s0.readReg64 Reg.x0, s0.readReg64 Reg.x1) SepProp.emp hpc hrun (by simp) h_sp_align)
    (fun sf _ _ hp => by simpa using hp)

theorem _root_.Arm64.Spec.rustOption64.intro {prog : Program} {entry : BitVec 64}
    {P : BitVec 64 → BitVec 64 → BitVec 32 → BitVec 64 → Prop}
    (h : ∀ (a : BitVec 64 × BitVec 64) (R : SepProp) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      ((s0.readReg64 Reg.x0 = a.1 ∧ s0.readReg64 Reg.x1 = a.2) ∧ (s0.mem ⊨ R)) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0
        (SubroutinePost (Spec.rustOption64 P) a R s0)) :
    subroutine_ok prog entry (Spec.rustOption64 P) :=
  subroutine_ok_intro fun a R s0 hpc hrun hpre hsp =>
    reaches_pc_mono (h a R s0 hpc hrun (by simpa using hpre) hsp)
      (fun _ _ _ hp => hp) (fun _ _ ho => False.elim ho)

theorem _root_.Arm64.Spec.rustOption64.mono {prog : Program} {entry : BitVec 64}
    {P Q : BitVec 64 → BitVec 64 → BitVec 32 → BitVec 64 → Prop}
    (h : subroutine_ok prog entry (Spec.rustOption64 P))
    (himp : ∀ a b disc payload, P a b disc payload → Q a b disc payload) :
    subroutine_ok prog entry (Spec.rustOption64 Q) :=
  subroutine_ok_mono_entails h (fun _ _ => Entails.refl _)
    (fun a _ sf => Entails.pure_mono (himp a.1 a.2 (sf.readReg32 Reg.x0) (sf.readReg64 Reg.x1)))

theorem _root_.Arm64.Spec.rustOption64.apply {prog : Program} {entry : BitVec 64}
    {P : BitVec 64 → BitVec 64 → BitVec 32 → BitVec 64 → Prop}
    (h : subroutine_ok prog entry (Spec.rustOption64 P)) {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0
      (fun sf => P (s0.readReg64 Reg.x0) (s0.readReg64 Reg.x1) (sf.readReg32 Reg.x0) (sf.readReg64 Reg.x1)) :=
  reaches_pc_mono
    (subroutine_ok_apply h (s0.readReg64 Reg.x0, s0.readReg64 Reg.x1) SepProp.emp hpc hrun (by simp) h_sp_align)
    (fun sf _ _ hp => by simpa using hp)

theorem _root_.Arm64.Spec.rustOption8.intro {prog : Program} {entry : BitVec 64}
    {P : BitVec 32 → BitVec 32 → BitVec 8 → Prop}
    (h : ∀ (c : BitVec 32) (R : SepProp) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      (s0.readReg32 Reg.x0 = c ∧ (s0.mem ⊨ R)) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0
        (SubroutinePost (Spec.rustOption8 P) c R s0)) :
    subroutine_ok prog entry (Spec.rustOption8 P) :=
  subroutine_ok_intro fun c R s0 hpc hrun hpre hsp =>
    reaches_pc_mono (h c R s0 hpc hrun (by simpa using hpre) hsp)
      (fun _ _ _ hp => hp) (fun _ _ ho => False.elim ho)

theorem _root_.Arm64.Spec.rustOption8.mono {prog : Program} {entry : BitVec 64}
    {P Q : BitVec 32 → BitVec 32 → BitVec 8 → Prop}
    (h : subroutine_ok prog entry (Spec.rustOption8 P))
    (himp : ∀ c disc payload, P c disc payload → Q c disc payload) :
    subroutine_ok prog entry (Spec.rustOption8 Q) :=
  subroutine_ok_mono_entails h (fun _ _ => Entails.refl _)
    (fun c _ sf => Entails.pure_mono (himp c (sf.readReg32 Reg.x0) ((sf.readReg32 Reg.x1).truncate 8)))

theorem _root_.Arm64.Spec.rustOption8.apply {prog : Program} {entry : BitVec 64}
    {P : BitVec 32 → BitVec 32 → BitVec 8 → Prop}
    (h : subroutine_ok prog entry (Spec.rustOption8 P)) {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0
      (fun sf => P (s0.readReg32 Reg.x0) (sf.readReg32 Reg.x0) ((sf.readReg32 Reg.x1).truncate 8)) :=
  reaches_pc_mono
    (subroutine_ok_apply h (s0.readReg32 Reg.x0) SepProp.emp hpc hrun (by simp) h_sp_align)
    (fun sf _ _ hp => by simpa using hp)

/-! ## Niche-optimized return rules -/

@[simp]
theorem decodeNiche64_zero : decodeNiche64 0#64 = none := rfl

@[simp]
theorem decodeNiche64_ne_zero {v : BitVec 64} (hv : v ≠ 0#64) :
    decodeNiche64 v = some v := by
  simp [decodeNiche64, hv]

@[simp]
theorem decodeNiche64_eq_none_iff (r : BitVec 64) :
    decodeNiche64 r = none ↔ r = 0#64 := by
  by_cases h : r = 0#64 <;> simp [decodeNiche64, h]

theorem _root_.Arm64.Spec.rustNiche64.intro {prog : Program} {entry : BitVec 64}
    {P : BitVec 64 → Option (BitVec 64) → Prop}
    (h : ∀ (a : BitVec 64) (R : SepProp) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      (s0.readReg64 Reg.x0 = a ∧ (s0.mem ⊨ R)) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0
        (SubroutinePost (Spec.rustNiche64 P) a R s0)) :
    subroutine_ok prog entry (Spec.rustNiche64 P) :=
  subroutine_ok_intro fun a R s0 hpc hrun hpre hsp =>
    reaches_pc_mono (h a R s0 hpc hrun (by simpa using hpre) hsp)
      (fun _ _ _ hp => hp) (fun _ _ ho => False.elim ho)

theorem _root_.Arm64.Spec.rustNiche64.mono {prog : Program} {entry : BitVec 64}
    {P Q : BitVec 64 → Option (BitVec 64) → Prop}
    (h : subroutine_ok prog entry (Spec.rustNiche64 P))
    (himp : ∀ a r, P a r → Q a r) :
    subroutine_ok prog entry (Spec.rustNiche64 Q) :=
  subroutine_ok_mono_entails h (fun _ _ => Entails.refl _)
    (fun a _ sf => Entails.pure_mono (himp a (decodeNiche64 (sf.readReg64 Reg.x0))))

theorem _root_.Arm64.Spec.rustNiche64.apply {prog : Program} {entry : BitVec 64}
    {P : BitVec 64 → Option (BitVec 64) → Prop}
    (h : subroutine_ok prog entry (Spec.rustNiche64 P)) {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0
      (fun sf => P (s0.readReg64 Reg.x0) (decodeNiche64 (sf.readReg64 Reg.x0))) :=
  reaches_pc_mono
    (subroutine_ok_apply h (s0.readReg64 Reg.x0) SepProp.emp hpc hrun (by simp) h_sp_align)
    (fun sf _ _ hp => by simpa using hp)

/-! ## Indirect aggregate return rules -/

theorem _root_.Arm64.Spec.rustSret.intro {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → BitVec 64 → BitVec 64 → State → Prop}
    {preMem : α → BitVec 64 → BitVec 64 → SepProp}
    {postRegs : α → BitVec 64 → BitVec 64 → State → State → Prop}
    {postMem : α → BitVec 64 → BitVec 64 → SepProp}
    (h : ∀ (x : α) (arg sret : BitVec 64) (R : SepProp) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      s0.readReg64 Reg.x0 = arg →
      s0.readReg64 Reg.x8 = sret →
      preRegs x arg sret s0 →
      (s0.mem ⊨ preMem x arg sret ∗ R) →
      s0.spAligned = true →
      reaches_pc prog (s0.readReg64 Reg.lr) s0
        (SubroutinePost (Spec.rustSret preRegs preMem postRegs postMem) (x, arg, sret) R s0)) :
    subroutine_ok prog entry (Spec.rustSret preRegs preMem postRegs postMem) :=
  Spec.split.intro fun (x, arg, sret) R s0 hpc hrun ⟨hx0, hx8, hpre⟩ hmem hsp =>
    h x arg sret R s0 hpc hrun hx0 hx8 hpre hmem hsp

theorem _root_.Arm64.Spec.rustSret.apply {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → BitVec 64 → BitVec 64 → State → Prop}
    {preMem : α → BitVec 64 → BitVec 64 → SepProp}
    {postRegs : α → BitVec 64 → BitVec 64 → State → State → Prop}
    {postMem : α → BitVec 64 → BitVec 64 → SepProp}
    (h : subroutine_ok prog entry (Spec.rustSret preRegs preMem postRegs postMem))
    (x : α) (arg sret : BitVec 64) (R : SepProp) {s0 : State}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 Reg.x0 = arg) (hx8 : s0.readReg64 Reg.x8 = sret)
    (hregs : preRegs x arg sret s0) (hmem : s0.mem ⊨ preMem x arg sret ∗ R)
    (h_sp_align : s0.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0 (fun sf =>
      postRegs x arg sret s0 sf ∧ (sf.mem ⊨ postMem x arg sret ∗ R) ∧ CallingConventionPreserved s0 sf) :=
  Spec.split.apply h (x, arg, sret) R hpc hrun ⟨hx0, hx8, hregs⟩ hmem h_sp_align

theorem _root_.Arm64.Spec.rustSret.frame {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → BitVec 64 → BitVec 64 → State → Prop}
    {preMem : α → BitVec 64 → BitVec 64 → SepProp}
    {postRegs : α → BitVec 64 → BitVec 64 → State → State → Prop}
    {postMem : α → BitVec 64 → BitVec 64 → SepProp}
    (h : subroutine_ok prog entry (Spec.rustSret preRegs preMem postRegs postMem))
    (F : α → BitVec 64 → BitVec 64 → SepProp) :
    subroutine_ok prog entry
      (Spec.rustSret preRegs
        (fun x arg sret => preMem x arg sret ∗ F x arg sret)
        postRegs
        (fun x arg sret => postMem x arg sret ∗ F x arg sret)) :=
  Spec.split.frame h fun (x, arg, sret) => F x arg sret

theorem _root_.Arm64.Spec.rustSret.mono {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs preRegs' : α → BitVec 64 → BitVec 64 → State → Prop}
    {preMem preMem' : α → BitVec 64 → BitVec 64 → SepProp}
    {postRegs postRegs' : α → BitVec 64 → BitVec 64 → State → State → Prop}
    {postMem postMem' : α → BitVec 64 → BitVec 64 → SepProp}
    (h : subroutine_ok prog entry (Spec.rustSret preRegs preMem postRegs postMem))
    (hpreR : ∀ x arg sret s0, preRegs' x arg sret s0 → preRegs x arg sret s0)
    (hpreM : ∀ x arg sret, preMem' x arg sret ⊢ preMem x arg sret)
    (hpostR : ∀ x arg sret s0 sf, postRegs x arg sret s0 sf → postRegs' x arg sret s0 sf)
    (hpostM : ∀ x arg sret, postMem x arg sret ⊢ postMem' x arg sret) :
    subroutine_ok prog entry (Spec.rustSret preRegs' preMem' postRegs' postMem') :=
  Spec.split.mono h
    (fun (x, arg, sret) s0 ⟨hx0, hx8, hr⟩ => ⟨hx0, hx8, hpreR x arg sret s0 hr⟩)
    (fun (x, arg, sret) => hpreM x arg sret)
    (fun (x, arg, sret) s0 sf hr => hpostR x arg sret s0 sf hr)
    (fun (x, arg, sret) => hpostM x arg sret)

end ProofLib
