/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import GeneratedLean.LibsignalSessionObj
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# `ext`-Generic Contract Program (`SP2Ext`) and Hook-Stack Framing

Defines `SP2Ext b ext := contractProg b ext` (`libsignalSessionCode.rebase b (Rust.withPanics ext)`),
panic-stub lookup (`panic_at_panicSymbol_ext`), stack-slack monotonicity (`Spec.withHookStack`),
and stacked allocator bundles (`AllocContractsX`), plus relocatable `[LibsignalPlacement]`
variants.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem L1 : True := trivial

/-! ## 1. `SP2Ext` (`contractProg b ext`) and Direct Address Helpers -/

/-- The `ext`-generic session program rebased at `b` with panic hooks `Rust.withPanics ext`.
Definitionally equal to `contractProg b ext`. -/
noncomputable abbrev SP2Ext (b : BitVec 64) (ext : String → Option (State → State)) : Program :=
  contractProg b ext

@[scoped simp]
theorem SP2Ext_eq_contractProg (b : BitVec 64) (ext : String → Option (State → State)) :
    SP2Ext b ext = contractProg b ext := rfl

theorem SP2Ext_fnAddr (b : BitVec 64) (ext : String → Option (State → State)) (sym : String) :
    (SP2Ext b ext).fnAddr sym = b + stubOff sym := by
  rw [Program.fnAddr_rebase]
  rfl

/-- Rewrite `subroutine_ok prog (prog.fnAddr sym) spec` to `subroutine_ok prog (b + off) spec`. -/
theorem sub_ok_at_of_fnAddr {α : Type} {prog : Program} {b off : BitVec 64} {sym : String}
    {spec : Spec α} (ha : prog.fnAddr sym = b + off)
    (h : subroutine_ok prog (prog.fnAddr sym) spec) :
    subroutine_ok prog (b + off) spec :=
  ha ▸ h

/-- Rewrite `subroutine_ok (contractProg b ext) (b + stubOff sym) spec` to a concrete offset `b + off`. -/
theorem sub_ok_at_of_stubOff {α : Type} {b : BitVec 64} {ext : String → Option (State → State)}
    {sym : String} {off : BitVec 64} {spec : Spec α}
    (hoff : stubOff sym = off)
    (h : subroutine_ok (contractProg b ext) (b + stubOff sym) spec) :
    subroutine_ok (SP2Ext b ext) (b + off) spec :=
  hoff ▸ h

/-- Rewrite `subroutine_ok (contractProg b ext) (b + stubOff hname) spec` to a caller-relative
call target `(SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k`. -/
theorem sub_ok_at_caller {α : Type} {b : BitVec 64} {ext : String → Option (State → State)}
    {name hname : String} {k : Nat} {spec : Spec α}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff hname)
    (h : subroutine_ok (contractProg b ext) (b + stubOff hname) spec) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k) spec := by
  have haddr : (SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k = b + stubOff hname := by
    rw [Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]
    rfl
  rw [haddr]
  exact h

/-! ## 2. Direct Panic-Stub Lookup on `SP2Ext b ext` -/

/-- Any panic symbol (`Rust.isPanicSymbol hname = true`) resolves to `some Rust.panicked` on `SP2Ext b ext`
at call distance `k` from caller `name`. -/
theorem panic_at_panicSymbol_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {name hname : String} {off k stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = stub)
    (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H hname)
    (hpan : Rust.isPanicSymbol hname = true) :
    (SP2Ext b ext).externAt? ((SP2Ext b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (P := libsignalSessionCode) (b := b) (hooks := ext)
    (name := name) (hname := hname) hfn hk hs hstub hpan

/-! ## 3. Stack-Slack Framing (`Spec.withHookStack` and Monotonicity) -/

/-- Lift `subroutine_ok_map` across `Spec.inImage img`. -/
theorem subroutine_ok_inImage_map' {α β : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (spec.inImage img))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (spec'.inImage img) := by
  refine subroutine_ok_map h (fun y R s0 hpre => ?_) h_no_panic h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfrozen, hpre'⟩ := hpre
  obtain ⟨x, R', hm, hpost⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost⟩
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfrozen, hm⟩

/-- Lift `subroutine_ok_map_panic` across `Spec.inImage img`. -/
theorem subroutine_ok_inImage_map_panic' {α β : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (spec.inImage img))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (spec'.inImage img) := by
  refine subroutine_ok_map_panic h (fun y R s0 hpre => ?_) h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfrozen, hpre'⟩ := hpre
  obtain ⟨x, R', hm, hpost, hpan⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost, hpan⟩
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfrozen, hm⟩

/-- Stack-slack framing for `Spec.withHookStack`: if a non-panicking subroutine satisfies
`(spec.withHookStack s1).inImage img` and `s1 ≤ s2 ≤ 2^64`, then it also satisfies
`(spec.withHookStack s2).inImage img` by framing the lower `s2 - s1` stack bytes across the call
via `ProofLib.stackAt_split_bottom`. -/
theorem subroutine_ok_inImage_withHookStack_mono {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((spec.withHookStack s1).inImage img))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry ((spec.withHookStack s2).inImage img) := by
  refine subroutine_ok_inImage_map' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit h_no_oom
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-! ## 4. Stacked Allocator Specifications & `AllocContractsX` -/

/-- Enrich a `Spec α` that owns `stackAt s.sp allocHookStack` (`4096`) with the remaining `12288`
bytes of `externStack` (`16384`). -/
def _root_.Arm64.Spec.withExternStackFromAlloc' {α : Type} (spec : Spec α) : Spec α where
  pre := fun x s => spec.pre x s ∗ memRegion (s.sp - 16384#64) 12288
  post := fun x s0 sf => spec.post x s0 sf ∗ memRegion (s0.sp - 16384#64) 12288
  onPanic := spec.onPanic
  onExit := spec.onExit

/-- `AllocContractsX img A ext`: contract-form allocator bundle on `SP2Ext img.base ext`
at `externStack = 16384`. -/
structure AllocContractsX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
    (((rustAllocSpec A).withExternStackFromAlloc').inImage img)
  dealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
    (((rustDeallocSpec A).withExternStackFromAlloc').inImage img)
  realloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
    (((rustReallocSpec A).withExternStackFromAlloc').inImage img)

/-- Call `__rustc::__rust_alloc` at caller-relative offset `k` on `SP2Ext img.base ext`. -/
theorem AllocContractsX.alloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (((rustAllocSpec A).withExternStackFromAlloc').inImage img) :=
  sub_ok_at_caller hk hA.alloc

/-- Call `__rustc::__rust_dealloc` (`rustDeallocSpec`) at caller-relative offset `k` on `SP2Ext img.base ext`. -/
theorem AllocContractsX.dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (((rustDeallocSpec A).withExternStackFromAlloc').inImage img) :=
  sub_ok_at_caller hk hA.dealloc

/-- Call `__rustc::__rust_realloc` at caller-relative offset `k` on `SP2Ext img.base ext`. -/
theorem AllocContractsX.realloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (((rustReallocSpec A).withExternStackFromAlloc').inImage img) :=
  sub_ok_at_caller hk hA.realloc

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed
set_option maxRecDepth 2000000

/-- Lift `subroutine_ok_map` across `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_map' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_map h (fun y R s0 hpre => ?_) h_no_panic h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨x, R', hm, hpost⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost⟩
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hm⟩

/-- Lift `subroutine_ok_map_panic` across `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_map_panic' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_map_panic h (fun y R s0 hpre => ?_) h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨x, R', hm, hpost, hpan⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost, hpan⟩
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hm⟩

/-- Lift `subroutine_ok_map` across `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_map' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCl pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl spec') := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_map' h0 hmap h_no_panic h_no_exit h_no_oom

/-- Lift `subroutine_ok_map_panic` across `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_map_panic' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCl pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl spec') := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_map_panic' h0 hmap h_no_exit h_no_oom

/-- Stack-slack framing for `Spec.withHookStack` under `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_withHookStack_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (spec.withHookStack s1)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCodeLoaded pl (spec.withHookStack s2)) := by
  refine subroutine_ok_withLsCodeLoaded_map' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit h_no_oom
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Stack-slack framing for `Spec.withHookStack` under `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_withHookStack_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCl pl (spec.withHookStack s1)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl (spec.withHookStack s2)) := by
  refine subroutine_ok_withLsCl_map' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit h_no_oom
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Frame `memRegion (s.sp - 16384#64) 12288` onto any non-panicking `subroutine_ok` (`withExternStackFromAlloc'`). -/
theorem subroutine_ok_withExternStackFromAlloc' {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec)
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry spec.withExternStackFromAlloc' := by
  refine subroutine_ok_map h (fun x R s0 hpre => ?_) h_no_panic h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  refine ⟨x, memRegion (s0.sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withExternStackFromAlloc'] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    dsimp only [Spec.withExternStackFromAlloc']
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Relocatable `[LibsignalPlacement]` counterpart of `Hooks2.AllocContractsX` (`withExternStackFromAlloc'`). -/
structure AllocContractsXPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpec A).withExternStackFromAlloc')
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustDeallocSpec A).withExternStackFromAlloc')
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustReallocSpec A).withExternStackFromAlloc')

theorem AllocContractsXPlaced.of_block0 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocSpec A).withExternStackFromAlloc'))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustDeallocSpec A).withExternStackFromAlloc'))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustReallocSpec A).withExternStackFromAlloc')) :
    AllocContractsXPlaced A H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  dealloc := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc

theorem AllocContractsXPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    AllocContractsXPlaced A H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller halloc))
  dealloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hdealloc))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hrealloc))

end Placed

end Proofs.libsignal.Hooks2
