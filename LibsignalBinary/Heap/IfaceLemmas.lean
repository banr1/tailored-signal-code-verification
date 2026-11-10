/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Iface
public import Arm64.Trusted.Spec.GlobalAlloc
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Caller-Side Helpers for `Iface`

State-predicate and pool/OOM transport combinators, OOM-preserving stack wrappers
(`Spec.withHookStackOom`, `Spec.withExternStackFromAllocOom'`, `rustCli*SpecWithStack`),
`.inImage` framing rules, and hook/entry-point bundle projections for `LibsignalBinary.Heap.Iface`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.IfaceLemmas

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)
open LibsignalBinary.Heap (PoolPreserved AllocCallPreserved OomPreserved
  RustLayoutOk NullAllowed RustCliAlloc rustCliAllocSpec rustCliDeallocSpec
  rustCliReallocSpec RustCliAllocHooks RustAllocAddrs RustCliAllocEntries)

/-! ## State Predicates and Pool/OOM Transport -/

theorem _root_.LibsignalBinary.Heap.PoolPreserved.symm {s₁ s₂ : State}
    (h : PoolPreserved s₁ s₂) : PoolPreserved s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem _root_.LibsignalBinary.Heap.PoolPreserved.of_vm {s₁ s₂ : State}
    (h : Rust.VmPreserved s₁ s₂) : PoolPreserved s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem _root_.LibsignalBinary.Heap.PoolPreserved.of_allocCallPreserved_brk {s0 sf : State}
    (h : AllocCallPreserved s0 sf) (hbrk : sf.brk = s0.brk) : PoolPreserved s0 sf :=
  ⟨h.2.2.2.2.1, hbrk, h.2.2.2.1⟩

theorem _root_.LibsignalBinary.Heap.AllocCallPreserved.refl (s : State) :
    AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem _root_.LibsignalBinary.Heap.AllocCallPreserved.trans {s₁ s₂ s₃ : State}
    (h12 : AllocCallPreserved s₁ s₂) (h23 : AllocCallPreserved s₂ s₃) :
    AllocCallPreserved s₁ s₃ :=
  ⟨h23.1.trans h12.1,
   h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

theorem _root_.LibsignalBinary.Heap.AllocCallPreserved.toOomPreserved {s0 sf : State}
    (h : AllocCallPreserved s0 sf) : OomPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem _root_.LibsignalBinary.Heap.OomPreserved.refl (s : State) :
    OomPreserved s s :=
  ⟨rfl, rfl, rfl⟩

theorem _root_.LibsignalBinary.Heap.OomPreserved.symm {s₁ s₂ : State}
    (h : OomPreserved s₁ s₂) : OomPreserved s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem _root_.LibsignalBinary.Heap.OomPreserved.trans {s₁ s₂ s₃ : State}
    (h12 : OomPreserved s₁ s₂) (h23 : OomPreserved s₂ s₃) :
    OomPreserved s₁ s₃ :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.trans h12.2.2⟩

theorem _root_.LibsignalBinary.Heap.RustLayoutOk.layoutOk {size align : Nat}
    (h : RustLayoutOk size align) : LayoutOk size align :=
  h.1

theorem _root_.LibsignalBinary.Heap.RustLayoutOk.align_le {size align : Nat}
    (h : RustLayoutOk size align) : align ≤ 2 ^ 31 :=
  h.2

theorem _root_.LibsignalBinary.Heap.RustLayoutOk.size_pos {size align : Nat}
    (h : RustLayoutOk size align) : 0 < size :=
  h.1.1

theorem _root_.LibsignalBinary.Heap.RustLayoutOk.size_add_align_le {size align : Nat}
    (h : RustLayoutOk size align) : size + align ≤ 2 ^ 63 :=
  h.1.2.2

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAlloc.pool_setFpsr (A : RustCliAlloc)
    (s : State) (f : BitVec 32) :
    A.pool (s.setFpsr f) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAlloc.pool_orFpsr (A : RustCliAlloc)
    (s : State) (f : BitVec 32) :
    A.pool (s.orFpsr f) = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAlloc.pool_nextOracle (A : RustCliAlloc)
    (s : State) :
    A.pool s.nextOracle = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩

@[simp, arm64_norm, wp_norm]
theorem _root_.LibsignalBinary.Heap.RustCliAlloc.pool_stepExclOracle (A : RustCliAlloc)
    (s : State) :
    A.pool s.stepExclOracle = A.pool s :=
  A.pool_transport _ _ ⟨rfl, rfl, rfl⟩

/-- Rewrite `A.pool s1` to `A.pool s2` inside a `SepWP` spatial context across `PoolPreserved s1 s2`. -/
theorem _root_.ProofLib.SepWP.transport_pool {A : RustCliAlloc} {s1 s2 : State}
    (hvm : PoolPreserved s1 s2)
    {prog : Program} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = A.pool s1 ∗ F := by sep_focus)
    (hnext : SepWP prog target_pc s2 (A.pool s2 ∗ F) post oom) :
    SepWP prog target_pc s2 P post oom :=
  SepWP.focus_weaken (by rw [A.pool_transport s1 s2 hvm]; exact Entails.refl _) hf hnext

/-- Panic-aware (`SepWPp`) counterpart of `SepWP.transport_pool`. -/
theorem _root_.ProofLib.SepWPp.transport_pool {A : RustCliAlloc} {s1 s2 : State}
    (hvm : PoolPreserved s1 s2)
    {prog : Program} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = A.pool s1 ∗ F := by sep_focus)
    (hnext : SepWPp prog ret s2 (A.pool s2 ∗ F) Q Qp oom) :
    SepWPp prog ret s2 P Q Qp oom :=
  SepWPp.congr_pre (hf.trans (congrArg (· ∗ F) (A.pool_transport s1 s2 hvm).symm)) hnext

abbrev transport_pool := @ProofLib.SepWP.transport_pool
abbrev wpp_transport_pool := @ProofLib.SepWPp.transport_pool

/-- Drop an intermediate call frame `F` and compose `OomPreserved s0 s1` with
`OomPreserved s1 sf` on an `.OutOfMemory` branch. -/
theorem satisfies_oomPreserved_frame {s0 s1 sf : State} {F R : SepProp}
    (h01 : OomPreserved s0 s1 := by refine ⟨rfl, rfl, rfl⟩)
    (ho : sf.mem ⊨ ⌜OomPreserved s1 sf⌝ ∗ (F ∗ R)) :
    sf.mem ⊨ ⌜OomPreserved s0 sf⌝ ∗ R := by
  have ho' : sf.mem ⊨ ⌜OomPreserved s1 sf⌝ ∗ R := Satisfies.drop_mid ho
  rw [satisfies_pure_sepConj] at ho' ⊢
  exact ⟨h01.trans ho'.1, ho'.2⟩

/-- Transport the `oom` obligation of `SepWP` from `⌜OomPreserved s0 sf⌝` to
`⌜OomPreserved s1 sf⌝` across an intermediate state `s1` with `OomPreserved s0 s1`
(e.g. after a call with `AllocCallPreserved s0 s1`). -/
theorem _root_.ProofLib.SepWP.transport_oom {s0 s1 : State}
    (h01 : OomPreserved s0 s1)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hnext : SepWP prog target_pc s P post (fun sf => ⌜OomPreserved s1 sf⌝)) :
    SepWP prog target_pc s P post (fun sf => ⌜OomPreserved s0 sf⌝) :=
  SepWP.of_reaches_pc fun _ hm =>
    reaches_pc_mono (SepWP.to_reaches_pc hnext hm)
      (fun _ _ _ hq => hq)
      (fun _ _ hoom_mem => by
        rw [satisfies_pure_sepConj] at hoom_mem ⊢
        exact ⟨h01.trans hoom_mem.1, hoom_mem.2⟩)

/-- Panic-aware (`SepWPp`) counterpart of `SepWP.transport_oom`. -/
theorem _root_.ProofLib.SepWPp.transport_oom {s0 s1 : State}
    (h01 : OomPreserved s0 s1)
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hnext : SepWPp prog ret s P Q Qp (fun sf => ⌜OomPreserved s1 sf⌝)) :
    SepWPp prog ret s P Q Qp (fun sf => ⌜OomPreserved s0 sf⌝) := by
  intro R hm hL
  rcases hnext R hm hL with ⟨sf, hsteps, hok | hpan | ⟨hoom_st, hoom_mem⟩⟩
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · rw [satisfies_pure_sepConj] at hoom_mem
    refine ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom_st, ?_⟩)⟩
    rw [satisfies_pure_sepConj]
    exact ⟨h01.trans hoom_mem.1, hoom_mem.2⟩

/-! ## OOM-Preserving Stack Wrappers -/

/-- Attach `stackAt s.sp hookStack` to a specification's precondition and postcondition while
preserving `onPanic`, `onExit`, and `onOom` (the OOM-preserving analogue of `Spec.withHookStack`). -/
def _root_.Arm64.Spec.withHookStackOom {α : Type} (spec : Spec α) (hookStack : Nat) : Spec α where
  pre := fun x s => spec.pre x s ∗ stackAt s.sp hookStack
  post := fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp hookStack
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

/-- Enrich a `Spec α` that owns `stackAt s.sp allocHookStack` (`4096`) with the remaining `12288`
bytes of `externStack` (`16384`), while preserving `onPanic`, `onExit`, and `onOom`
(the OOM-preserving analogue of `Spec.withExternStackFromAlloc'`). -/
def _root_.Arm64.Spec.withExternStackFromAllocOom' {α : Type} (spec : Spec α) : Spec α where
  pre := fun x s => spec.pre x s ∗ memRegion (s.sp - 16384#64) 12288
  post := fun x s0 sf => spec.post x s0 sf ∗ memRegion (s0.sp - 16384#64) 12288
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

abbrev withHookStackOom := @Arm64.Spec.withHookStackOom
abbrev withExternStackFromAllocOom' := @Arm64.Spec.withExternStackFromAllocOom'

@[simp] theorem withHookStackOom_pre {α : Type} (spec : Spec α) (n : Nat) (x : α) (s : State) :
    (spec.withHookStackOom n).pre x s = (spec.pre x s ∗ stackAt s.sp n) := rfl
@[simp] theorem withHookStackOom_post {α : Type} (spec : Spec α) (n : Nat) (x : α) (s0 sf : State) :
    (spec.withHookStackOom n).post x s0 sf = (spec.post x s0 sf ∗ stackAt s0.sp n) := rfl
@[simp] theorem withHookStackOom_onPanic {α : Type} (spec : Spec α) (n : Nat) :
    (spec.withHookStackOom n).onPanic = spec.onPanic := rfl
@[simp] theorem withHookStackOom_onExit {α : Type} (spec : Spec α) (n : Nat) :
    (spec.withHookStackOom n).onExit = spec.onExit := rfl
@[simp] theorem withHookStackOom_onOom {α : Type} (spec : Spec α) (n : Nat) :
    (spec.withHookStackOom n).onOom = spec.onOom := rfl

@[simp] theorem withExternStackFromAllocOom'_pre {α : Type} (spec : Spec α) (x : α) (s : State) :
    spec.withExternStackFromAllocOom'.pre x s =
      (spec.pre x s ∗ memRegion (s.sp - 16384#64) 12288) := rfl
@[simp] theorem withExternStackFromAllocOom'_post {α : Type} (spec : Spec α) (x : α)
    (s0 sf : State) :
    spec.withExternStackFromAllocOom'.post x s0 sf =
      (spec.post x s0 sf ∗ memRegion (s0.sp - 16384#64) 12288) := rfl
@[simp] theorem withExternStackFromAllocOom'_onPanic {α : Type} (spec : Spec α) :
    spec.withExternStackFromAllocOom'.onPanic = spec.onPanic := rfl
@[simp] theorem withExternStackFromAllocOom'_onExit {α : Type} (spec : Spec α) :
    spec.withExternStackFromAllocOom'.onExit = spec.onExit := rfl
@[simp] theorem withExternStackFromAllocOom'_onOom {α : Type} (spec : Spec α) :
    spec.withExternStackFromAllocOom'.onOom = spec.onOom := rfl

def rustCliAllocSpecWithStack (A : RustCliAlloc) (zeroed : Bool) (stk : Nat) :
    Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align⌝ ∗
      A.pool s ∗ stackAt s.sp stk
  post := fun (size, align) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

def rustCliDeallocSpecWithStack (A : RustCliAlloc) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp stk
  post := fun _ s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool sf ∗ stackAt s0.sp stk

def rustCliReallocSpecWithStack (A : RustCliAlloc) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new⌝ ∗
      A.pool s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (p, old, align, new, bs) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun _ s0 sf => ⌜OomPreserved s0 sf⌝

/-! ## OOM-Preserving `.inImage` Map and Stack-Framing Combinators -/

/-- Drop a framed middle assertion `F` under `⊨` and weaken the left assertion by `P ⊢ P'`. -/
theorem satisfies_drop_mid_entails {P P' F R : SepProp} {m : Memory}
    (hent : P ⊢ P') (h : m ⊨ P ∗ (F ∗ R)) : m ⊨ P' ∗ R :=
  Satisfies.mono (sepConj_mono_left hent) (Satisfies.drop_mid h)

/-- Lift `ProofLib.subroutine_ok_map_oom'` across `Spec.inImage img` (OOM-preserving analogue of
`Hooks2.Defs.subroutine_ok_inImage_map'`). -/
theorem subroutine_ok_inImage_map_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (spec.inImage img))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (spec'.inImage img) := by
  refine subroutine_ok_map_oom' h (fun y R s0 hpre => ?_) h_no_panic h_no_exit
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfrozen, hpre'⟩ := hpre
  obtain ⟨x, R', hm, hpost, hoom⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost, hoom⟩
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfrozen, hm⟩

/-- Panic- and OOM-preserving lift across `Spec.inImage img` (analogue of
`Hooks2.Defs.subroutine_ok_inImage_map_panic'`). -/
theorem subroutine_ok_inImage_map_panic_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (spec.inImage img))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') →
          (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (spec'.inImage img) := by
  refine subroutine_ok_outcome_intro fun y R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfrozen, hpre'⟩ := hpre
  obtain ⟨x, R', hm, hpost, hpan, hoom⟩ := hmap y R s0 hpre'
  have hm_img : s0.mem ⊨ (spec.inImage img).pre x s0 ∗ R' := by
    simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfrozen, hm⟩
  refine h.mono_outcome x R' s0 hpc hrun hm_img hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex, hq⟩ | ⟨ho_st, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost sf hq⟩
  · exact Or.inr (Or.inl ⟨hp_st, hpan sf hq⟩)
  · exact False.elim (h_no_exit x code R' s0 sf hex hq)
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hoom sf hq⟩))

/-- Frame-carving `.inImage` consequence rule with direct entailment `spec.onOom ⊢ spec'.onOom`
(dropping the carved frame `F` on `.OutOfMemory` via `Satisfies.drop_mid`). -/
theorem subroutine_ok_inImage_frame_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (spec.inImage img))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (F : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ (F ∗ R)) ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_oom : ∀ x y s0 sf, spec.onOom x s0 sf ⊢ spec'.onOom y s0 sf := by
      intro _ _ _ _; first
        | exact Entails.refl _
        | exact Entails.pure_left fun hf => False.elim hf)
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (spec'.inImage img) :=
  subroutine_ok_inImage_map_oom' h
    (fun y R s0 hpre =>
      let ⟨x, F, hm, hpost⟩ := hmap y R s0 hpre
      ⟨x, F ∗ R, hm, hpost, fun sf ho => satisfies_drop_mid_entails (h_oom x y s0 sf) ho⟩)
    h_no_panic h_no_exit

/-- Panic- and OOM-preserving frame-carving `.inImage` consequence rule with direct entailment
`spec.onOom ⊢ spec'.onOom`. -/
theorem subroutine_ok_inImage_frame_panic_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (spec.inImage img))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (F : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_oom : ∀ x y s0 sf, spec.onOom x s0 sf ⊢ spec'.onOom y s0 sf := by
      intro _ _ _ _; first
        | exact Entails.refl _
        | exact Entails.pure_left fun hf => False.elim hf)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (spec'.inImage img) :=
  subroutine_ok_inImage_map_panic_oom' h
    (fun y R s0 hpre =>
      let ⟨x, F, hm, hpost, hpan⟩ := hmap y R s0 hpre
      ⟨x, F ∗ R, hm, hpost, hpan, fun sf ho => satisfies_drop_mid_entails (h_oom x y s0 sf) ho⟩)
    h_no_exit

/-- General frame-entailment rule across normal return, panic, exit, and OOM where abnormal
outcomes drop the carved frame `Frame x s0` via `Satisfies.drop_mid` and weaken by `⊢`. -/
theorem subroutine_ok_frame_oom' {α : Type} {prog : Program} {entry : BitVec 64}
    {specSmall specBig : Spec α} (Frame : α → State → SepProp)
    (h : subroutine_ok prog entry specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢ specSmall.pre x s0 ∗ Frame x s0)
    (hpost : ∀ x s0 sf, specSmall.post x s0 sf ∗ Frame x s0 ⊢ specBig.post x s0 sf)
    (hpan : ∀ x s0 sf, specSmall.onPanic x s0 sf ⊢ specBig.onPanic x s0 sf := by
      intro _ _ _; first
        | exact Entails.refl _
        | exact Entails.pure_left fun hf => False.elim hf)
    (hex : ∀ x code s0 sf, specSmall.onExit x code s0 sf ⊢ specBig.onExit x code s0 sf := by
      intro _ _ _ _; first
        | exact Entails.refl _
        | exact Entails.pure_left fun hf => False.elim hf)
    (hoom : ∀ x s0 sf, specSmall.onOom x s0 sf ⊢ specBig.onOom x s0 sf := by
      intro _ _ _; first
        | exact Entails.refl _
        | exact Entails.pure_left fun hf => False.elim hf) :
    subroutine_ok prog entry specBig := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hm hal => ?_
  have hm' : s0.mem ⊨ specSmall.pre x s0 ∗ (Frame x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hm
  refine h.mono_outcome x (Frame x s0 ∗ R) s0 hpc hrun hm' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hp⟩ | ⟨ho_st, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hp
  · exact Or.inr (Or.inl ⟨hp_st, satisfies_drop_mid_entails (hpan x s0 sf) hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, satisfies_drop_mid_entails (hex x code s0 sf) hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, satisfies_drop_mid_entails (hoom x s0 sf) hp⟩))

/-- Stack-slack monotonicity for `Spec.withHookStackOom` (`s1 ≤ s2 ≤ 2 ^ 64`), preserving
normal return, panic, exit, and OOM unconditionally. -/
theorem subroutine_ok_withHookStackOom_mono {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (spec.withHookStackOom s1)) :
    subroutine_ok prog entry (spec.withHookStackOom s2) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1)) h ?_ ?_
  · intro x s0
    have hsplit : s2 = s1 + (s2 - s1) := by omega
    have hstack := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rw [← hsplit] at hstack
    dsimp only [Spec.withHookStackOom]
    rw [hstack]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    have hsplit : s2 = s1 + (s2 - s1) := by omega
    have hstack := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rw [← hsplit] at hstack
    dsimp only [Spec.withHookStackOom]
    rw [hstack]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Stack-slack monotonicity for `(spec.withHookStackOom s).inImage img` (`s1 ≤ s2 ≤ 2 ^ 64`),
preserving normal return, panic, exit, and OOM unconditionally. -/
theorem subroutine_ok_inImage_withHookStackOom_mono {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((spec.withHookStackOom s1).inImage img)) :
    subroutine_ok prog entry ((spec.withHookStackOom s2).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1)) h ?_ ?_
  · intro x s0
    have hsplit : s2 = s1 + (s2 - s1) := by omega
    have hstack := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rw [← hsplit] at hstack
    dsimp only [Spec.inImage, Spec.withHookStackOom]
    rw [hstack]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    have hsplit : s2 = s1 + (s2 - s1) := by omega
    have hstack := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rw [← hsplit] at hstack
    dsimp only [Spec.inImage, Spec.withHookStackOom]
    rw [hstack]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_withExternStackFromAllocOom' {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry spec.withExternStackFromAllocOom' :=
  subroutine_ok_frame_oom' (fun _ s0 => memRegion (s0.sp - 16384#64) 12288) h
    (fun _ _ => Entails.refl _) (fun _ _ _ => Entails.refl _)

theorem subroutine_ok_inImage_withExternStackFromAllocOom' {α : Type} {prog : Program}
    {entry : BitVec 64} {img : Obj.Image} {spec : Spec α}
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (spec.withExternStackFromAllocOom'.inImage img) :=
  subroutine_ok_frame_oom' (fun _ s0 => memRegion (s0.sp - 16384#64) 12288) h
    (fun _ _ => Entails.of_eq (by dsimp only [Spec.inImage, Spec.withExternStackFromAllocOom']; sep_ac_rfl))
    (fun _ _ _ => Entails.refl _)

private theorem stackAt_split_from_allocHookStack (sp : BitVec 64) {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ stackAt sp allocHookStack := by
  have hsplit : stk = allocHookStack + (stk - allocHookStack) := by
    dsimp only [allocHookStack] at hle ⊢; omega
  have h0 := ProofLib.stackAt_split_bottom sp allocHookStack (stk - allocHookStack)
    (by dsimp only [allocHookStack] at hle ⊢; omega)
  rwa [← hsplit] at h0

theorem subroutine_ok_rustCliAlloc_withStack {prog : Program} {entry : BitVec 64}
    {A : RustCliAlloc} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliAllocSpec A zeroed)) :
    subroutine_ok prog entry (rustCliAllocSpecWithStack A zeroed stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align⟩ s0
    dsimp only [rustCliAllocSpec, rustCliAllocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align⟩ s0 sf
    dsimp only [rustCliAllocSpec, rustCliAllocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliAlloc_withStack {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustCliAlloc} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliAllocSpec A zeroed).inImage img)) :
    subroutine_ok prog entry ((rustCliAllocSpecWithStack A zeroed stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align⟩ s0
    dsimp only [Spec.inImage, rustCliAllocSpec, rustCliAllocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align⟩ s0 sf
    dsimp only [Spec.inImage, rustCliAllocSpec, rustCliAllocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliDealloc_withStack {prog : Program} {entry : BitVec 64}
    {A : RustCliAlloc} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliDeallocSpec A)) :
    subroutine_ok prog entry (rustCliDeallocSpecWithStack A stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, size, align⟩ s0
    dsimp only [rustCliDeallocSpec, rustCliDeallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align⟩ s0 sf
    dsimp only [rustCliDeallocSpec, rustCliDeallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliDealloc_withStack {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustCliAlloc} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliDeallocSpec A).inImage img)) :
    subroutine_ok prog entry ((rustCliDeallocSpecWithStack A stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, size, align⟩ s0
    dsimp only [Spec.inImage, rustCliDeallocSpec, rustCliDeallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align⟩ s0 sf
    dsimp only [Spec.inImage, rustCliDeallocSpec, rustCliDeallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliRealloc_withStack {prog : Program} {entry : BitVec 64}
    {A : RustCliAlloc} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliReallocSpec A)) :
    subroutine_ok prog entry (rustCliReallocSpecWithStack A stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs⟩ s0
    dsimp only [rustCliReallocSpec, rustCliReallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs⟩ s0 sf
    dsimp only [rustCliReallocSpec, rustCliReallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliRealloc_withStack {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustCliAlloc} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliReallocSpec A).inImage img)) :
    subroutine_ok prog entry ((rustCliReallocSpecWithStack A stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs⟩ s0
    dsimp only [Spec.inImage, rustCliReallocSpec, rustCliReallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs⟩ s0 sf
    dsimp only [Spec.inImage, rustCliReallocSpec, rustCliReallocSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## `RustCliAllocHooks` and `RustCliAllocEntries` Projections -/

@[simp] theorem isPanicSymbol_rust_alloc :
    Rust.isPanicSymbol "__rustc::__rust_alloc" = false := by
  simp [Rust.isPanicSymbol]

@[simp] theorem isPanicSymbol_rust_dealloc :
    Rust.isPanicSymbol "__rustc::__rust_dealloc" = false := by
  simp [Rust.isPanicSymbol]

@[simp] theorem isPanicSymbol_rust_realloc :
    Rust.isPanicSymbol "__rustc::__rust_realloc" = false := by
  simp [Rust.isPanicSymbol]

private theorem hookSat_withPanics {α : Type} {hooks : String → Option (State → State)}
    {hname : String} {spec : Spec α}
    (hnp : Rust.isPanicSymbol hname = false) (hsat : HookSat hooks hname spec) :
    HookSat (Rust.withPanics hooks) hname spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩

private theorem subroutine_ok_of_hookSat {α : Type} {prog : Program} {entry : BitVec 64}
    {hooks : String → Option (State → State)} {hname : String} {spec : Spec α}
    (hext : prog.externAt? entry = hooks hname) (hsat : HookSat hooks hname spec) :
    subroutine_ok prog entry spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk (hext.trans hf) hok

/-- `RustCliAllocHooks` is preserved under `Rust.withPanics` because none of the three Rust
allocator symbols is a panic symbol. -/
theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.withPanics {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks) :
    RustCliAllocHooks A (Rust.withPanics hooks) :=
  ⟨hookSat_withPanics isPanicSymbol_rust_alloc hH.alloc,
   hookSat_withPanics isPanicSymbol_rust_dealloc hH.dealloc,
   hookSat_withPanics isPanicSymbol_rust_realloc hH.realloc⟩

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.alloc_ok {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_alloc") :
    subroutine_ok prog entry (rustCliAllocSpec A false) :=
  subroutine_ok_of_hookSat hext hH.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.dealloc_ok {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_dealloc") :
    subroutine_ok prog entry (rustCliDeallocSpec A) :=
  subroutine_ok_of_hookSat hext hH.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.realloc_ok {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {prog : Program} {entry : BitVec 64}
    (hext : prog.externAt? entry = hooks "__rustc::__rust_realloc") :
    subroutine_ok prog entry (rustCliReallocSpec A) :=
  subroutine_ok_of_hookSat hext hH.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.alloc_ok_stub {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {code : Program} {b : BitVec 64} {stub : Nat}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X "__rustc::__rust_alloc") :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub) (rustCliAllocSpec A false) :=
  hook_ok_stub hs hstub hH.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.dealloc_ok_stub {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {code : Program} {b : BitVec 64} {stub : Nat}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X "__rustc::__rust_dealloc") :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub) (rustCliDeallocSpec A) :=
  hook_ok_stub hs hstub hH.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.realloc_ok_stub {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {code : Program} {b : BitVec 64} {stub : Nat}
    (hs : stub < 2 ^ 64)
    (hstub : ∀ X, (code.rebase 0 X).hookAtOff? stub = X "__rustc::__rust_realloc") :
    subroutine_ok (code.rebase b hooks) (b + BitVec.ofNat 64 stub) (rustCliReallocSpec A) :=
  hook_ok_stub hs hstub hH.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.alloc_ok_at {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_alloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocSpec A false) :=
  hook_ok_at hfn hk hs hstub isPanicSymbol_rust_alloc hH.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.dealloc_ok_at {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_dealloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocSpec A) :=
  hook_ok_at hfn hk hs hstub isPanicSymbol_rust_dealloc hH.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.realloc_ok_at {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_realloc") :
    subroutine_ok (P.rebase b (Rust.withPanics hooks))
      ((P.rebase b (Rust.withPanics hooks)).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocSpec A) :=
  hook_ok_at hfn hk hs hstub isPanicSymbol_rust_realloc hH.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.alloc_ok_at_raw {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_alloc") :
    subroutine_ok (P.rebase b hooks)
      ((P.rebase b hooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocSpec A false) :=
  hook_ok_at_raw hfn hk hs hstub hH.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.dealloc_ok_at_raw {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_dealloc") :
    subroutine_ok (P.rebase b hooks)
      ((P.rebase b hooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocSpec A) :=
  hook_ok_at_raw hfn hk hs hstub hH.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.realloc_ok_at_raw {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {P : Program} {b : BitVec 64} {name : String} {off k stub : Nat}
    (hfn : P.fnOff name = off) (hk : off + k = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (P.rebase 0 H).hookAtOff? stub = H "__rustc::__rust_realloc") :
    subroutine_ok (P.rebase b hooks)
      ((P.rebase b hooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocSpec A) :=
  hook_ok_at_raw hfn hk hs hstub hH.realloc

/-- Bridge `RustCliAllocHooks A hooks` into `RustCliAllocEntries A prog addrs` whenever
`prog.externAt?` resolves `addrs.{alloc,dealloc,realloc}` to the three allocator hooks. -/
theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.toEntries {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {prog : Program} {addrs : RustAllocAddrs}
    (halloc : prog.externAt? addrs.alloc = hooks "__rustc::__rust_alloc")
    (hdealloc : prog.externAt? addrs.dealloc = hooks "__rustc::__rust_dealloc")
    (hrealloc : prog.externAt? addrs.realloc = hooks "__rustc::__rust_realloc") :
    RustCliAllocEntries A prog addrs :=
  ⟨hH.alloc_ok halloc, hH.dealloc_ok hdealloc, hH.realloc_ok hrealloc⟩

/-- Bridge `RustCliAllocHooks A hooks` on `code.rebase b hooks` at stub offsets
`(allocStub, deallocStub, reallocStub)` into `RustCliAllocEntries`. -/
theorem _root_.LibsignalBinary.Heap.RustCliAllocHooks.toEntries_stubs {A : RustCliAlloc}
    {hooks : String → Option (State → State)} (hH : RustCliAllocHooks A hooks)
    {code : Program} {b : BitVec 64} {allocStub deallocStub reallocStub : Nat}
    (hsA : allocStub < 2 ^ 64)
    (hstubA : ∀ X, (code.rebase 0 X).hookAtOff? allocStub = X "__rustc::__rust_alloc")
    (hsD : deallocStub < 2 ^ 64)
    (hstubD : ∀ X, (code.rebase 0 X).hookAtOff? deallocStub = X "__rustc::__rust_dealloc")
    (hsR : reallocStub < 2 ^ 64)
    (hstubR : ∀ X, (code.rebase 0 X).hookAtOff? reallocStub = X "__rustc::__rust_realloc") :
    RustCliAllocEntries A (code.rebase b hooks)
      ⟨b + BitVec.ofNat 64 allocStub,
       b + BitVec.ofNat 64 deallocStub,
       b + BitVec.ofNat 64 reallocStub⟩ :=
  ⟨hH.alloc_ok_stub hsA hstubA,
   hH.dealloc_ok_stub hsD hstubD,
   hH.realloc_ok_stub hsR hstubR⟩

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.alloc_inImage {A : RustCliAlloc}
    {P : Program} {addrs : RustAllocAddrs} (hE : RustCliAllocEntries A P addrs)
    (img : Obj.Image) :
    subroutine_ok P addrs.alloc ((rustCliAllocSpec A false).inImage img) :=
  subroutine_ok_inImage img hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.dealloc_inImage {A : RustCliAlloc}
    {P : Program} {addrs : RustAllocAddrs} (hE : RustCliAllocEntries A P addrs)
    (img : Obj.Image) :
    subroutine_ok P addrs.dealloc ((rustCliDeallocSpec A).inImage img) :=
  subroutine_ok_inImage img hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.realloc_inImage {A : RustCliAlloc}
    {P : Program} {addrs : RustAllocAddrs} (hE : RustCliAllocEntries A P addrs)
    (img : Obj.Image) :
    subroutine_ok P addrs.realloc ((rustCliReallocSpec A).inImage img) :=
  subroutine_ok_inImage img hE.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.alloc_externStack {A : RustCliAlloc}
    {P : Program} {addrs : RustAllocAddrs} (hE : RustCliAllocEntries A P addrs) :
    subroutine_ok P addrs.alloc (rustCliAllocSpec A false).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.dealloc_externStack {A : RustCliAlloc}
    {P : Program} {addrs : RustAllocAddrs} (hE : RustCliAllocEntries A P addrs) :
    subroutine_ok P addrs.dealloc (rustCliDeallocSpec A).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.realloc_externStack {A : RustCliAlloc}
    {P : Program} {addrs : RustAllocAddrs} (hE : RustCliAllocEntries A P addrs) :
    subroutine_ok P addrs.realloc (rustCliReallocSpec A).withExternStackFromAllocOom' :=
  subroutine_ok_withExternStackFromAllocOom' hE.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.alloc_externStack_inImage
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.alloc
      (((rustCliAllocSpec A false).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img hE.alloc_externStack

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.dealloc_externStack_inImage
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.dealloc
      (((rustCliDeallocSpec A).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img hE.dealloc_externStack

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.realloc_externStack_inImage
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) (img : Obj.Image) :
    subroutine_ok P addrs.realloc
      (((rustCliReallocSpec A).withExternStackFromAllocOom').inImage img) :=
  subroutine_ok_inImage img hE.realloc_externStack

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.alloc_withStack
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc (rustCliAllocSpecWithStack A false stk) :=
  subroutine_ok_rustCliAlloc_withStack hle hbound hE.alloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.dealloc_withStack
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc (rustCliDeallocSpecWithStack A stk) :=
  subroutine_ok_rustCliDealloc_withStack hle hbound hE.dealloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.realloc_withStack
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc (rustCliReallocSpecWithStack A stk) :=
  subroutine_ok_rustCliRealloc_withStack hle hbound hE.realloc

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.alloc_withStack_inImage
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.alloc ((rustCliAllocSpecWithStack A false stk).inImage img) :=
  subroutine_ok_inImage img (hE.alloc_withStack hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.dealloc_withStack_inImage
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.dealloc ((rustCliDeallocSpecWithStack A stk).inImage img) :=
  subroutine_ok_inImage img (hE.dealloc_withStack hle hbound)

theorem _root_.LibsignalBinary.Heap.RustCliAllocEntries.realloc_withStack_inImage
    {A : RustCliAlloc} {P : Program} {addrs : RustAllocAddrs}
    (hE : RustCliAllocEntries A P addrs) (img : Obj.Image) {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addrs.realloc ((rustCliReallocSpecWithStack A stk).inImage img) :=
  subroutine_ok_inImage img (hE.realloc_withStack hle hbound)

/-! ## Transport Focus Check -/

section SmokeCheck

example (A : RustCliAlloc) (s1 s2 : State) (hvm : PoolPreserved s1 s2)
    (prog : Program) (pc : BitVec 64) (X Y : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWP prog pc s2 (A.pool s2 ∗ (X ∗ Y)) post oom) :
    SepWP prog pc s2 (X ∗ A.pool s1 ∗ Y) post oom :=
  SepWP.transport_pool hvm (hnext := h)

example (A : RustCliAlloc) (s1 s2 : State) (hvm : PoolPreserved s1 s2)
    (prog : Program) (ret : BitVec 64) (X Y : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp)
    (h : SepWPp prog ret s2 (A.pool s2 ∗ (X ∗ Y)) Q Qp oom) :
    SepWPp prog ret s2 (X ∗ A.pool s1 ∗ Y) Q Qp oom :=
  SepWPp.transport_pool hvm (hnext := h)

end SmokeCheck

end LibsignalBinary.Heap.IfaceLemmas
