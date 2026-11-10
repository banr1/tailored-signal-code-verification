/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Defs
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# `LibsignalCodeLoaded` Threading Combinators for `Prost.MessageMerge`

`SepWPp` sequencing and framed-call combinators threading `LibsignalCodeLoaded` (`withLsCodeLoaded`),
together with monotonicity lifting to `withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet

/-- Run a `SepWP` segment to `mid` while preserving `LibsignalCodeLoaded pl` (`KeepsFrozen`). -/
theorem SepWPp.of_sepWP_lscl_mm {prog : Program} {pl : Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.seq_frozen
    (fun _ _ (hc : LibsignalCodeLoaded pl _) hkf => hc.of_keepsFrozen hkf) hinv h

/-- Framed `SepWPp.call` to a `(withLsCodeLoaded pl spec)` callee, threading `LibsignalCodeLoaded pl` to `hnext`. -/
theorem SepWPp.call_frame_lscl_mm {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hinv : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = spec.post x s sm ∗ F) Qp := by
    refine ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr
      (fun R hm => ?_) hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      hoom
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-- Irreducible wrapper around `⌜LibsignalCodeLoaded pl s.mem⌝` so `wpp_init` keeps it as a spatial atom
without shifting pure-hypothesis names (`h_1`, `h_2`, `h_3`, `h`). -/
@[irreducible]
def lsclProp (pl : Obj.MultiPlacement) (s : State) : SepProp :=
  ⌜LibsignalCodeLoaded pl s.mem⌝

/-- Variant of `withLsCodeLoaded` that wraps `LibsignalCodeLoaded pl s.mem` in `lsclProp` for `wpp_init`. -/
def withLsclProp {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α where
  pre := fun x s => lsclProp pl s ∗ spec.pre x s
  post := spec.post
  onExit := spec.onExit
  onPanic := spec.onPanic
  onOom := spec.onOom

theorem subroutine_ok_withLsCodeLoaded_of_withLsclProp {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsclProp pl spec)) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  obtain ⟨hcl, hp⟩ := extract_withLsCodeLoaded hp
  dsimp only [withLsclProp]
  unfold lsclProp
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hcl, hp⟩

theorem SepWPp.elim_lsclProp {prog : Program} {pl : Obj.MultiPlacement} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : LibsignalCodeLoaded pl s.mem → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (lsclProp pl s ∗ P) Q Qp := by
  unfold lsclProp
  exact ProofLib.SepWPp.pure_elim h

/-- Weaken a `withLsCodeLoaded` contract on `prog` to `withLsCodeRoLoaded`. -/
theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm {α : Type} {prog : Program}
    {pl : Obj.MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcro.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

end CryptoVerification.SpqrV1.Prost.MessageMerge
