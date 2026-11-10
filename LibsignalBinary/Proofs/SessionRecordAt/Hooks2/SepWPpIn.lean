/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SepWPp` Wrappers Carrying Code-Loaded Invariants

Defines panic-aware weakest-precondition wrappers that thread frozen-code and symbol-table
invariants across basic-block steps and external stub calls:
* `SepWPpIn img`: threads `img.FrozenLoaded s ∧ s.symtab = img.symtab` for `.inImage img`
  subroutine contracts on `SP2Ext`.
* `SepWPpLsCl pl` and `SepWPpLsCro pl`: thread `LibsignalCodeLoaded pl s.mem` and
  `LibsignalCodeRoLoaded pl s.mem` for relocatable `[LibsignalPlacement]` proofs.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib CryptoVerification

/-- `SepWPp` carrying the frozen-image / symbol-table invariant `img.FrozenLoaded s ∧ s.symtab = img.symtab`. -/
def SepWPpIn (img : Obj.Image) (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop) : Prop :=
  img.FrozenLoaded s → s.symtab = img.symtab → SepWPp prog ret s P Q Qp

namespace SepWPpIn

variable {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem of_sepWP {mid : BitVec 64}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpIn img prog ret sm Pm Q Qp)) :
    SepWPpIn img prog ret s P Q Qp :=
  fun hF hsym => ProofLib.SepWPp.of_sepWP_frozen hF hsym h

theorem of_sepWP_ret (h : SepWP prog ret s P Q) : SepWPpIn img prog ret s P Q Qp :=
  fun _ _ => SepWPp.of_sepWP_ret h

theorem done (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPpIn img prog ret s P Q Qp :=
  fun _ _ => SepWPp.done hpc hrun hq

theorem weaken_pre {P' : SepProp} (hent : P ⊢ P') (h : SepWPpIn img prog ret s P' Q Qp) :
    SepWPpIn img prog ret s P Q Qp :=
  fun hF hsym => SepWPp.weaken_pre hent (h hF hsym)

theorem pure_elim {φ : Prop} (h : φ → SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  fun hF hsym => SepWPp.pure_elim fun hφ => h hφ hF hsym

theorem exists_elim {α : Sort _} {P : α → SepProp}
    (h : ∀ a, SepWPpIn img prog ret s (P a) Q Qp) :
    SepWPpIn img prog ret s (∃∗ a, P a) Q Qp :=
  fun hF hsym => SepWPp.exists_elim fun a => h a hF hsym

theorem call {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpIn img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  exact SepWPp.call_wpp_frozen hcall (x := x) (F := F) hF hsym hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan) hnext
    (fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)

theorem call_inImage {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpIn img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  refine SepWPp.call_wpp_frozen hcall (x := x) (F := F) hF hsym hpc hrun hsp hlr ?_ hexit
    (fun sf hpan _ => hpanic sf hpan) hnext
    (fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)
  intro R hm
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hF, hsym⟩, hpre R hm⟩

end SepWPpIn

theorem subroutine_ok_inImage_of_sepWPpIn {img : Obj.Image} {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpIn img prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (spec.inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, hpre⟩
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  exact ⟨P, Fr, hm, hwp hF hsym⟩

/-! ## Relocatable `[LibsignalPlacement]` wrappers (`SepWPpLsCl` and `SepWPpLsCro`) -/

section Placed

open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded withLsCodeRoLoaded extract_withLsCodeRoLoaded)

/-- Wraps `spec` with `⌜LibsignalCodeRoLoaded pl ·.mem⌝` in both precondition and postcondition. -/
abbrev withLsRoClIn {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeRoLoaded pl s0.mem⌝
    post := fun x s0 sf => ⌜LibsignalCodeRoLoaded pl sf.mem⌝ ∗ spec.post x s0 sf }

/-- `SepWPp` carrying the relocatable code-loaded invariant `LibsignalCodeLoaded pl s.mem`. -/
def SepWPpLsCl (pl : Obj.MultiPlacement) (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop) : Prop :=
  LibsignalCodeLoaded pl s.mem → SepWPp prog ret s P Q Qp

namespace SepWPpLsCl

variable {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem of_sepWP {mid : BitVec 64}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpLsCl pl prog ret sm Pm Q Qp)) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

theorem of_sepWP_ret (h : SepWP prog ret s P Q) : SepWPpLsCl pl prog ret s P Q Qp :=
  fun _ => SepWPp.of_sepWP_ret h

theorem done (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  fun _ => SepWPp.done hpc hrun hq

theorem weaken_pre {P' : SepProp} (hent : P ⊢ P') (h : SepWPpLsCl pl prog ret s P' Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  fun hcl => SepWPp.weaken_pre hent (h hcl)

theorem pure_elim {φ : Prop} (h : φ → SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  fun hcl => SepWPp.pure_elim fun hφ => h hφ hcl

theorem exists_elim {α : Sort _} {P : α → SepProp}
    (h : ∀ a, SepWPpLsCl pl prog ret s (P a) Q Qp) :
    SepWPpLsCl pl prog ret s (∃∗ a, P a) Q Qp :=
  fun hcl => SepWPp.exists_elim fun a => h a hcl

theorem call {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F) Qp :=
    SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)
  intro hcl R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hcl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem call_withLsCodeLoaded {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F) Qp := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)
    intro R hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hcl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem call_withLsCl {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  call_withLsCodeLoaded
    (subroutine_ok_mono hcall (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2))
    hpc hrun hsp hlr hpre hexit hpanic hnext hoom

end SepWPpLsCl

theorem subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl {pl : Obj.MultiPlacement} {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpLsCl pl prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  exact ⟨P, Fr, hm, hwp hcl⟩

/-- `SepWPp` carrying both `LibsignalCodeLoaded` and `LibsignalRoLoaded` (`LibsignalCodeRoLoaded pl s.mem`). -/
def SepWPpLsCro (pl : Obj.MultiPlacement) (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop) : Prop :=
  LibsignalCodeRoLoaded pl s.mem → SepWPp prog ret s P Q Qp

namespace SepWPpLsCro

variable {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem of_sepWP {mid : BitVec 64}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpLsCro pl prog ret sm Pm Q Qp)) :
    SepWPpLsCro pl prog ret s P Q Qp := by
  intro hcrl R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

theorem of_sepWP_ret (h : SepWP prog ret s P Q) : SepWPpLsCro pl prog ret s P Q Qp :=
  fun _ => SepWPp.of_sepWP_ret h

theorem done (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPpLsCro pl prog ret s P Q Qp :=
  fun _ => SepWPp.done hpc hrun hq

theorem weaken_pre {P' : SepProp} (hent : P ⊢ P') (h : SepWPpLsCro pl prog ret s P' Q Qp) :
    SepWPpLsCro pl prog ret s P Q Qp :=
  fun hcrl => SepWPp.weaken_pre hent (h hcrl)

theorem pure_elim {φ : Prop} (h : φ → SepWPpLsCro pl prog ret s P Q Qp) :
    SepWPpLsCro pl prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  fun hcrl => SepWPp.pure_elim fun hφ => h hφ hcrl

theorem exists_elim {α : Sort _} {P : α → SepProp}
    (h : ∀ a, SepWPpLsCro pl prog ret s (P a) Q Qp) :
    SepWPpLsCro pl prog ret s (∃∗ a, P a) Q Qp :=
  fun hcrl => SepWPp.exists_elim fun a => h a hcrl

theorem call_withLsCodeRoLoaded {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCro pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpLsCro pl prog ret s P Q Qp := by
  intro hcrl
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F) Qp := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)
    intro R hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hpre R hm⟩
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem call_withLsCl {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCro pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpLsCro pl prog ret s P Q Qp :=
  call_withLsCodeRoLoaded
    (subroutine_ok_mono hcall
      (fun _ _ _ hp => by
        obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [withLsCl]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨hcrl.1, hpre⟩)
      (fun _ _ _ _ hq => by
        dsimp only [withLsCl, withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2))
    hpc hrun hsp hlr hpre hexit hpanic hnext hoom

theorem call_withLsRoCl {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry (withLsRoClIn pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCro pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPpLsCro pl prog ret s P Q Qp :=
  call_withLsCodeRoLoaded
    (subroutine_ok_mono hcall (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsRoClIn, withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2))
    hpc hrun hsp hlr hpre hexit hpanic hnext hoom

end SepWPpLsCro

theorem subroutine_ok_withLsCodeRoLoaded_of_sepWPpLsCro {pl : Obj.MultiPlacement} {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpLsCro pl prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  exact ⟨P, Fr, hm, hwp hcrl⟩

end Placed

end Proofs.libsignal.Hooks2
