/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.InImageKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public meta import ProofLib
public meta import LibsignalBinary.Proofs.Common.InImageKit
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `wp_call_lscro`: Separation-Logic Call Combinators for `withLsCodeRoLoaded`

Provides `SepWP` and `SepWPp` call lemmas and the `wp_call_lscro` tactic for `withLsCodeRoLoaded`,
`withLsRoCl`, `withLsCodeLoaded`, `withLsCl`, and plain callees under `[LibsignalPlacement]`, keeping
`LibsignalCodeRoLoaded` opaque to `simp` and threading `hcrl_sf` to the continuation.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj ProofLib
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi

/-! ## Call lemmas -/

theorem lscro_of_mem_eq {pl : MultiPlacement} {m m' : Memory}
    (h : StoreKit.LibsignalCodeRoLoaded pl m) (heq : m' = m) :
    StoreKit.LibsignalCodeRoLoaded pl m' := by
  rw [heq]; exact h

theorem satisfies_withLsCodeRoLoaded_pre {α : Type} {pl : MultiPlacement} {spec : Spec α}
    {x : α} {s : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (StoreKit.withLsCodeRoLoaded pl spec).pre x s ∗ R := by
  show s.mem ⊨ (spec.pre x s ∗ ⌜StoreKit.LibsignalCodeRoLoaded pl s.mem⌝) ∗ R
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcrl, hpre⟩

theorem satisfies_withLsRoCl_pre {α : Type} {pl : MultiPlacement} {spec : Spec α}
    {x : α} {s : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (StoreKit.withLsRoCl pl spec).pre x s ∗ R :=
  satisfies_withLsCodeRoLoaded_pre hcrl hpre

/-- Framed call to a plain `spec` callee in `SepWP`, threading `StoreKit.LibsignalCodeRoLoaded`. -/
theorem SepWP.call_lscro_plain {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  StoreKit.sepWP_seq_lscro (mid := ret_pc) hcrl
    (ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp hlr hpre h_no_panic h_no_exit
      (fun sf hpcf hrunf hspf hcsf =>
        ProofLib.SepWP.done hpcf hrunf (hnext sf hpcf hrunf hspf hcsf))
      (fun R' sf ho h => (not_satisfies_false_sepConj (h_no_oom (F ∗ R') sf ho h)).elim))

/-- Framed call to a `StoreKit.withLsCodeRoLoaded pl spec` callee in `SepWP`. -/
theorem SepWP.call_withLsCodeRoLoaded {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  SepWP.call_lscro_plain (spec := StoreKit.withLsCodeRoLoaded pl spec) (x := x) hcall hcrl
    hpc hrun hsp hlr (fun R hm => satisfies_withLsCodeRoLoaded_pre hcrl (hpre R hm))
    h_no_panic h_no_exit hnext h_no_oom

/-- Framed call to a `StoreKit.withLsRoCl pl spec` callee in `SepWP` (strips the pure
`LibsignalCodeRoLoaded` post conjunct so `spec.post` is exposed cleanly). -/
theorem SepWP.call_withLsRoCl {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  have hcall_cro : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded pl spec) :=
    subroutine_ok_mono hcall (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [StoreKit.withLsRoCl, StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  SepWP.call_withLsCodeRoLoaded (x := x) hcall_cro hcrl hpc hrun hsp hlr hpre
    h_no_panic h_no_exit hnext h_no_oom

/-- Framed call to a plain `spec` callee in `SepWPp`, threading `StoreKit.LibsignalCodeRoLoaded`. -/
theorem SepWPp.call_lscro_plain {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ |
    ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (not_satisfies_false_sepConj (h_no_oom _ sm hoom hpost)).elim

/-- Framed call to a `StoreKit.withLsCodeRoLoaded pl spec` callee in `SepWPp`. -/
theorem SepWPp.call_withLsCodeRoLoaded {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_lscro_plain (spec := StoreKit.withLsCodeRoLoaded pl spec) (x := x) hcall hcrl
    hpc hrun hsp hlr (fun R hm => satisfies_withLsCodeRoLoaded_pre hcrl (hpre R hm))
    hexit hpanic hnext h_no_oom

/-- Framed call to a `StoreKit.withLsRoCl pl spec` callee in `SepWPp`. -/
theorem SepWPp.call_withLsRoCl {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  have hcall_cro : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded pl spec) :=
    subroutine_ok_mono hcall (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [StoreKit.withLsRoCl, StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  SepWPp.call_withLsCodeRoLoaded (x := x) hcall_cro hcrl hpc hrun hsp hlr hpre
    hexit hpanic hnext h_no_oom

/-- Framed call to a `withLsCodeLoaded pl spec` callee in `SepWP`. -/
theorem SepWP.call_withLsCodeLoaded {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  SepWP.call_withLsCodeRoLoaded (x := x)
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcall) hcrl
    hpc hrun hsp hlr hpre h_no_panic h_no_exit hnext h_no_oom

/-- Framed call to a `withLsCl pl spec` callee in `SepWP`. -/
theorem SepWP.call_withLsCl {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (CryptoVerification.withLsCl pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post :=
  have hcall_cl : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono hcall (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [CryptoVerification.withLsCl, withLsCodeLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  SepWP.call_withLsCodeLoaded (x := x) hcall_cl hcrl hpc hrun hsp hlr hpre
    h_no_panic h_no_exit hnext h_no_oom

/-- Framed call to a `withLsCodeLoaded pl spec` callee in `SepWPp`. -/
theorem SepWPp.call_withLsCodeLoaded {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_withLsCodeRoLoaded (x := x)
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcall) hcrl
    hpc hrun hsp hlr hpre hexit hpanic hnext h_no_oom

/-- Framed call to a `withLsCl pl spec` callee in `SepWPp`. -/
theorem SepWPp.call_withLsCl {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (CryptoVerification.withLsCl pl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  have hcall_cl : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono hcall (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [CryptoVerification.withLsCl, withLsCodeLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  SepWPp.call_withLsCodeLoaded (x := x) hcall_cl hcrl hpc hrun hsp hlr hpre
    hexit hpanic hnext h_no_oom

/-! ## `wp_call_lscro` tactic -/

open Lean Elab Tactic Meta

meta def lscroKitMentionsInv (e : Expr) : Bool :=
  (e.find? fun t => t.isConst &&
    ["LibsignalCodeRoLoaded", "LibsignalCodeLoaded", "LibsignalRoLoaded",
     "LibsignalFrozen", "ImgCallInv", "FrozenInv"].contains
       (inImageKitLastStr t.constName!)).isSome

meta partial def lscroKitFindPl? (ty : Expr) : Option Expr :=
  let ty := ty.consumeMData
  if ty.getAppNumArgs == 2 && ty.getAppFn.isConst &&
      ["LibsignalCodeRoLoaded", "LibsignalCodeLoaded", "LibsignalRoLoaded",
       "LibsignalFrozen"].contains (inImageKitLastStr ty.getAppFn.constName!) then
    some (ty.getArg! 0)
  else if ty.isAppOfArity ``And 2 then
    (lscroKitFindPl? (ty.getArg! 0)).orElse fun _ => lscroKitFindPl? (ty.getArg! 1)
  else none

meta def lscroKitInvKind? (φ : Expr) : Option (Bool × Expr) :=
  let φ := φ.consumeMData
  if φ.getAppNumArgs == 2 && φ.getAppFn.isConst then
    let nm := inImageKitLastStr φ.getAppFn.constName!
    if nm == "LibsignalCodeRoLoaded" then some (true, φ.getArg! 0)
    else if nm == "LibsignalCodeLoaded" then some (false, φ.getArg! 0)
    else none
  else none

meta def lscroKitClearInvHyps : TacticM Unit := do
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut acc : Array FVarId := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOf ``Arm64.subroutine_ok then continue
      if lscroKitMentionsInv ty then acc := acc.push decl.fvarId
    return acc
  let g' ← g.tryClearMany fvs
  replaceMainGoal [g']

inductive LscroCallKind | plain | codeRo | roCl | codeOnly | clOnly

meta def lscroKitDeconstructSpec (specE : Expr) : MetaM (Option (LscroCallKind × Expr × Expr)) := do
  let specWhnf := (← whnf specE).consumeMData
  if !specWhnf.isAppOfArity ``Arm64.Spec.mk 6 then return none
  let αE := specWhnf.getArg! 0
  let preE := specWhnf.getArg! 1
  let postE := specWhnf.getArg! 2
  let panicE := specWhnf.getArg! 3
  let exitE := specWhnf.getArg! 4
  let oomE := specWhnf.getArg! 5
  let preRes? ← lambdaBoundedTelescope preE 2 fun xs preBody => do
    if xs.size != 2 then return none
    let b := preBody.consumeMData
    if !b.isAppOfArity ``Arm64.SepProp.sepConj 2 then return none
    let rhs := (b.getArg! 1).consumeMData
    if !rhs.isAppOfArity ``Arm64.SepProp.pure 1 then return none
    let some (isCodeRo, plE) := lscroKitInvKind? (rhs.getArg! 0) | return none
    let cleanPre ← mkLambdaFVars xs (b.getArg! 0)
    return some (isCodeRo, plE, cleanPre)
  let some (isCodeRo, plE, cleanPre) := preRes? | return none
  let (hasPostInv, cleanPost) ← lambdaBoundedTelescope postE 3 fun ys postBody => do
    if ys.size != 3 then return (false, postE)
    let b := postBody.consumeMData
    if !b.isAppOfArity ``Arm64.SepProp.sepConj 2 then return (false, postE)
    let lhs := (b.getArg! 0).consumeMData
    if !lhs.isAppOfArity ``Arm64.SepProp.pure 1 then return (false, postE)
    let some _ := lscroKitInvKind? (lhs.getArg! 0) | return (false, postE)
    return (true, ← mkLambdaFVars ys (b.getArg! 1))
  let kind := match isCodeRo, hasPostInv with
    | true, false => LscroCallKind.codeRo
    | true, true => LscroCallKind.roCl
    | false, false => LscroCallKind.codeOnly
    | false, true => LscroCallKind.clOnly
  let cleanSpec := mkAppN (mkConst ``Arm64.Spec.mk) #[αE, cleanPre, cleanPost, panicE, exitE, oomE]
  return some (kind, ← instantiateMVars plE, ← instantiateMVars cleanSpec)

meta def lscroKitCall (tacName : String) (hcall hcrl : Term) (arg? : Option Term) :
    TacticM Unit := do
  let g0 ← getMainGoal
  let gty := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData
  let isWPp ← if gty.isAppOfArity ``SepWPp 7 then pure true
    else if gty.isAppOfArity ``SepWP 6 then pure false
    else throwError "{tacName}: goal is not `SepWP …` / `SepWPp …`"
  let sGoal := gty.getArg! 2
  let (kind, plE, cleanSpec?) : LscroCallKind × Expr × Option Expr ←
      g0.withContext <| withoutModifyingState do
    let e ← Tactic.elabTerm hcall none
    let ty ← whnfR (← instantiateMVars (← inferType e))
    if !ty.isAppOfArity ``Arm64.subroutine_ok 4 then
      throwError "{tacName}: `{hcall}` is not a `subroutine_ok` hypothesis:{indentExpr ty}"
    let specE := (ty.getArg! 3).consumeMData
    if let some (k, pl, cs) ← lscroKitDeconstructSpec specE then
      return (k, pl, some cs)
    let hty ← instantiateMVars (← inferType (← Tactic.elabTerm hcrl none))
    let some pl := lscroKitFindPl? hty
      | throwError "{tacName}: cannot read `MultiPlacement` off `{hcrl} : {hty}`"
    return (LscroCallKind.plain, ← instantiateMVars pl, none)
  let hcrlId ← freshIdent `hcrl_call
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlSfId ← freshIdent `hcrl_sf
  let sStx ← g0.withContext (Term.exprToSyntax sGoal)
  let plStx ← g0.withContext (Term.exprToSyntax plE)
  let haveStx ← `(tactic|
    have $hcrlId:ident :
        CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded
          $plStx ($sStx).mem := by
      first
        | with_reducible exact $hcrl
        | exact ⟨($hcrl).1, ($hcrl).2⟩
        | exact lscro_of_mem_eq $hcrl (by simp only [arm64_norm, wp_norm]; done)
        | exact lscro_of_mem_eq ⟨($hcrl).1, ($hcrl).2⟩
            (by simp only [arm64_norm, wp_norm]; done))
  if !(← tryTacticCatchRuntimeBool (evalTactic haveStx)) then
    throwError "{tacName}: could not establish `LibsignalCodeRoLoaded pl s.mem` from `{hcrl}`."
  let lemmaName : Name := match isWPp, kind with
    | false, .plain => ``SepWP.call_lscro_plain
    | false, .codeRo => ``SepWP.call_withLsCodeRoLoaded
    | false, .roCl => ``SepWP.call_withLsRoCl
    | false, .codeOnly => ``SepWP.call_withLsCodeLoaded
    | false, .clOnly => ``SepWP.call_withLsCl
    | true, .plain => ``SepWPp.call_lscro_plain
    | true, .codeRo => ``SepWPp.call_withLsCodeRoLoaded
    | true, .roCl => ``SepWPp.call_withLsRoCl
    | true, .codeOnly => ``SepWPp.call_withLsCodeLoaded
    | true, .clOnly => ``SepWPp.call_withLsCl
  let lem := mkCIdent lemmaName
  let applyStx ← match cleanSpec?, arg? with
    | some cs, some a =>
      let csStx ← g0.withContext (Term.exprToSyntax cs)
      `(tactic| apply ($lem (spec := $csStx) $hcall $hcrlId (x := $a)))
    | some cs, none =>
      let csStx ← g0.withContext (Term.exprToSyntax cs)
      `(tactic| apply ($lem (spec := $csStx) $hcall $hcrlId))
    | none, some a => `(tactic| apply ($lem $hcall $hcrlId (x := $a)))
    | none, none => `(tactic| apply ($lem $hcall $hcrlId))
  evalTactic applyStx
  inImageKitCloseSetup tacName
  let gs ← getGoals
  let gPre :: gA :: gB :: gCont :: rest := gs
    | throwError "{tacName}: unexpected subgoals after call-site setup"
  setGoals [gPre]
  lscroKitClearInvHyps
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  inImageKitDestructureSat
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  let preLeft ← getGoals
  let mut side : List MVarId := []
  if isWPp then
    setGoals [gA]
    inImageKitClearByName hcrlId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hcrlId.getId
    let gB' ← getMainGoal
    gB'.setTag `panic
    side := side ++ [gB']
  else
    setGoals [gA]
    inImageKitClearByName hcrlId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hcrlId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
  setGoals [gCont]
  inImageKitClearByName hcrlId.getId
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlSfId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  if isWPp then inImageKitElimSpatialWPp hspId else wpElimSpatialContext hspId
  let contGoals ← getGoals
  let mut restOpen : List MVarId := []
  for m in rest do
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    if ty.consumeMData.isAppOfArity ``autoParam 2 then
      let m' ← m.replaceTargetDefEq (ty.consumeMData.getArg! 0)
      let saved ← saveState
      setGoals [m']
      if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_close_oom_default))) then
        if (← getGoals).isEmpty then continue
      saved.restore
      restOpen := restOpen ++ [m']
    else
      restOpen := restOpen ++ [m]
  let preOpen ← preLeft.filterM fun (m : MVarId) => not <$> m.isAssigned
  let sideOpen ← side.filterM fun (m : MVarId) => not <$> m.isAssigned
  setGoals (contGoals ++ preOpen ++ sideOpen ++ restOpen)

syntax (name := wpCallLscro) "wp_call_lscro" ppSpace colGt term:max ppSpace colGt term:max
  (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_call_lscro $hcall $hcrl) => lscroKitCall "wp_call_lscro" hcall hcrl none
  | `(tactic| wp_call_lscro $hcall $hcrl $arg) =>
    lscroKitCall "wp_call_lscro" hcall hcrl (some arg)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
