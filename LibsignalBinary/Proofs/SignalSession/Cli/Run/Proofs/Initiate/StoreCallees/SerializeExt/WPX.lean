/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.Common.InImageKit -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs -- shake: keep
public meta import ProofLib.SepLogic.WPp -- shake: keep

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

/-!
# Panic-Aware Weakest Precondition with Image Call Invariant

Wraps `SepWPp` with `ImgCallInv img` so instruction steps and `.inImage` calls thread
`Obj.Image.FrozenLoaded` without unfolding it in local tactic states.
-/

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64
open ProofLib
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells

private theorem sepWPp_mono {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (hq : ∀ sf Pf, sf.pc = ret → Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hpan | hoom⟩
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hpc hQ⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

/-- Panic-aware weakest precondition carrying `ImgCallInv img` across all instructions and `.inImage`
    calls without exposing `Obj.Image.FrozenLoaded` in local tactic contexts. -/
def SepWPpX (img : Obj.Image) (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop)
    (oom : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  ImgCallInv img s →
    SepWPp prog ret s P (fun sf Pf => ImgCallInv img sf ∧ Q sf Pf) Qp oom

namespace SepWPpX

theorem done {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv _R hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hinv, hq⟩⟩

theorem panic {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) :
    SepWPpX img prog ret s P Q Qp oom :=
  fun _ => SepWPp.panic hrun hext hqp

theorem exists_elim {α : Type} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {Φ : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPpX img prog ret s (Φ a) Q Qp) :
    SepWPpX img prog ret s (∃∗ a, Φ a) Q Qp :=
  fun hinv => SepWPp.exists_elim fun a => h a hinv

theorem pure_elim {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  fun hinv => SepWPp.pure_elim fun hφ => h hφ hinv

theorem weaken_pre {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hp : P ⊢ P') (h : SepWPpX img prog ret s P' Q Qp) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv => SepWPp.weaken_pre hp (h hinv)

theorem mono {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPpX img prog ret s P Q Qp)
    (hq : ∀ sf Pf, sf.pc = ret → Q sf Pf → Q' sf Pf) :
    SepWPpX img prog ret s P Q' Qp :=
  fun hinv => sepWPp_mono (h hinv) fun sf Pf hpc ⟨hinv_sf, hQ⟩ => ⟨hinv_sf, hq sf Pf hpc hQ⟩

theorem of_sepWP {img : Obj.Image} {prog : Program} (mid : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpX img prog ret sm Pm Q Qp)) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv R hm hL => by
    rcases h.elim hm hL with ⟨sm, hst1, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
    · obtain ⟨sf, hst2, hout⟩ :=
        hcont (ImgCallInv.of_steps hinv hst1) R hmm (hst1.codeLoaded hL)
      exact ⟨sf, hst1.trans hst2, hout⟩
    · exact ⟨sm, hst1, Or.inr (Or.inr hoom)⟩

theorem of_sepWP_inv {img : Obj.Image} {prog : Program} (mid : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ImgCallInv img s → SepWP prog mid s P (fun sm Pm => SepWPpX img prog ret sm Pm Q Qp)) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv R hm hL => by
    rcases (h hinv).elim hm hL with ⟨sm, hst1, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
    · obtain ⟨sf, hst2, hout⟩ :=
        hcont (ImgCallInv.of_steps hinv hst1) R hmm (hst1.codeLoaded hL)
      exact ⟨sf, hst1.trans hst2, hout⟩
    · exact ⟨sm, hst1, Or.inr (Or.inr hoom)⟩

theorem of_sepWP_ret {img : Obj.Image} {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog ret s P Q) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv R hm hL => by
    rcases h.elim hm hL with ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hoom⟩
    · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, ImgCallInv.of_steps hinv hst, hQ⟩⟩
    · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

theorem of_sepWP_ret_inv {img : Obj.Image} {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ImgCallInv img s → SepWP prog ret s P Q) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv R hm hL => by
    rcases (h hinv).elim hm hL with ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hoom⟩
    · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, ImgCallInv.of_steps hinv hst, hQ⟩⟩
    · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

theorem call {α : Type} {img : Obj.Image} {prog : Program}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpX img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv =>
    SepWPp.call_inImage (x := x) (F := F) hcall hinv hpc hrun hsp hlr hpre hexit hpanic
      (fun sf h1 h2 h3 h4 hinv_sf => hnext sf h1 h2 h3 h4 hinv_sf)
      h_no_oom

end SepWPpX

/-- Concrete CPS midpoint cut inside `SepWP` that carries `ImgCallInv img` across store instructions
    while preserving the concrete stepped state record upon closing with `SepWP.done`. -/
theorem sepWP_cut_inv {img : Obj.Image} {prog : Program} (mid : BitVec 64)
    {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hst1, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · rcases (hcont (ImgCallInv.of_steps hinv hst1)).elim hmm (hst1.codeLoaded hL) with
      ⟨sf, hst2, hout⟩
    exact ⟨sf, Steps.trans hst1 hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

theorem subroutine_ok_of_sepWPpX {α : Type} {img : Obj.Image} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpX img prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (spec.inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ spec.pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  obtain ⟨P, Fr, hm, hwpx⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P, Fr, hm, sepWPp_mono (hwpx hinv) ?_⟩
  intro sf P_f _ hpost
  exact hpost.2

theorem subroutine_ok_inImage_iff_right {α : Type} {img : Obj.Image} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry
      { pre := fun x s => spec.pre x s ∗ ⌜ImgCallInv img s⌝
        post := spec.post
        onExit := spec.onExit
        onPanic := spec.onPanic
        onOom := spec.onOom }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (spec.pre x s0 ∗ ⌜ImgCallInv img s0⌝) ∗ R := by
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ spec.pre x s0) ∗ R at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  exact h.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem subroutine_ok_inImage_of_ok {α : Type} {img : Obj.Image} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ spec.pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

theorem sepWPp_of_sepWPpX {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (h : SepWPpX img prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_mono (h hinv) fun _ _ _ hq => hq.2

theorem subroutine_ok_frame_weaken_inImage {α : Type} {img : Obj.Image} {prog : Program}
    {entry : BitVec 64} {inner outer : Spec α}
    (frame : α → State → SepProp)
    (h : subroutine_ok prog entry (inner.inImage img))
    (hpre : ∀ x s0, outer.pre x s0 ⊢ inner.pre x s0 ∗ frame x s0)
    (hpost : ∀ x s0 sf, inner.post x s0 sf ∗ frame x s0 ⊢ outer.post x s0 sf)
    (hpanic : ∀ x s0 sf, inner.onPanic x s0 sf ∗ frame x s0 ⊢ outer.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, inner.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, inner.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry (outer.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hm hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ outer.pre x s0) ∗ R at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hinv, hm⟩
  have hm_in : s0.mem ⊨ (inner.inImage img).pre x s0 ∗ (frame x s0 ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hm
  refine h.mono_outcome x (frame x s0 ∗ R) s0 hpc hrun hm_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpanic x s0 sf)) hq
  · dsimp only [Spec.inImage] at hq
    rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage] at hq
    rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

open Lean Elab Tactic Meta in
private meta def findLatestInvIdent? (g : MVarId) : TacticM (Option (Ident × FVarId)) :=
  g.withContext do
    let mut found : Option (Ident × FVarId) := none
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let dty ← instantiateMVars decl.type
        if (inImageKitFindImg? dty).isSome then
          found := some (mkIdent decl.userName, decl.fvarId)
    return found

open Lean Elab Tactic Meta in
private meta def wpxCallCore (tacName : String) (hcall : Term) (arg? : Option Term) : TacticM Unit := do
  let g0 ← getMainGoal
  let gty ← g0.withContext do instantiateMVars (← g0.getType)
  let gty := gty.consumeMData
  if gty.isAppOfArity ``SepWPpX 8 then
    let oldInvs ← g0.withContext do
      let mut acc : Array FVarId := #[]
      for decl in (← getLCtx) do
        if !decl.isImplementationDetail then
          let dty ← instantiateMVars decl.type
          if (inImageKitFindImg? dty).isSome then
            acc := acc.push decl.fvarId
      return acc
    if !oldInvs.isEmpty then
      let gClean ← g0.tryClearMany oldInvs
      setGoals [gClean]
    let imgE := gty.getArg! 0
    let progE := gty.getArg! 1
    let retE := gty.getArg! 2
    let qE := gty.getArg! 5
    let qpE := gty.getArg! 6
    let oomE := gty.getArg! 7
    let hinvId ← freshIdent `hinv_wpx
    let hSymId ← freshIdent `hsym_wpx
    evalTactic (← `(tactic| intro $hinvId:ident))
    evalTactic (← `(tactic| (
      have $hSymId:ident := ($hinvId).2
      try simp only [wp_norm, arm64_norm] at $hSymId:ident)))
    inImageKitCall tacName hcall hinvId arg?
    let gsRaw ← getGoals
    let mut gs : List MVarId := []
    for m0 in gsRaw do
      setGoals [m0]
      evalTactic (← `(tactic| try clear $hSymId:ident))
      gs := gs ++ (← getGoals)
    let mut out : List MVarId := []
    for m in gs do
      let ty ← m.withContext do instantiateMVars (← m.getType)
      let ty := ty.consumeMData
      if ty.isAppOfArity ``ProofLib.SepWPp 7 then
        let m' ← m.withContext do
          let sfE := ty.getArg! 2
          let pPost := ty.getArg! 3
          let mut sfInvFv? : Option FVarId := none
          let mut otherInvs : Array FVarId := #[]
          for decl in (← getLCtx) do
            if !decl.isImplementationDetail then
              let dty ← instantiateMVars decl.type
              if (inImageKitFindImg? dty).isSome then
                let dtyC := dty.consumeMData
                if dtyC.getAppNumArgs == 2 && (← isDefEq (dtyC.getArg! 1) sfE) then
                  sfInvFv? := some decl.fvarId
                else
                  otherInvs := otherInvs.push decl.fvarId
          match sfInvFv? with
          | some sfFv =>
            let mClean ← m.tryClearMany otherInvs
            let (_, revGoal) ← mClean.revert #[sfFv]
            let foldedTy := mkAppN (mkConst ``SepWPpX) #[imgE, progE, retE, sfE, pPost, qE, qpE, oomE]
            revGoal.replaceTargetDefEq foldedTy
          | none =>
            pure m
        out := out ++ [m']
      else
        let savedPan ← saveState
        setGoals [m]
        let closedPan ← tryTacticCatchRuntimeBool do
          evalTactic (← `(tactic| (
            intro _sf _hpan
            try (intro (_R : SepProp))
            intro _hm
            wp_unfold_specs
            try dsimp only [CryptoVerification.E2E.Record.Serialization.allocPanic] at _hm ⊢
            first
            | refine Satisfies.mono (sepConj_mono_left ?_) _hm
            | (rw [← sepConj_assoc]; refine Satisfies.mono (sepConj_mono_left ?_) _hm)
            simp only [sepConj_assoc]
            apply Entails.pure_left
            rintro ⟨_haf, _hpref⟩
            refine Entails.pure_right ⟨?_, ?_⟩ (entails_anyHeap _)
            · unfold CryptoVerification.LibsignalTripleRatchet.allocFailedIn at _haf ⊢
              simp only [wp_norm, arm64_norm] at _haf ⊢
              first | exact _haf | (rw [‹_ = _.trace›] at _haf; exact _haf) | (simp only [*] at _haf ⊢)
            · simp only [wp_norm, arm64_norm] at _hpref ⊢
              first | exact _hpref | (rw [‹_ = _.trace›] at _hpref; exact _hpref) | (simp only [*] at _hpref ⊢))))
          if !(← getGoals).isEmpty then
            throwError "unsolved panic subgoals"
        if !closedPan then
          savedPan.restore
          out := out ++ [m]
    setGoals out
  else if gty.isAppOfArity ``ProofLib.SepWP 6 then
    let some (hinvId, oldFv) ← findLatestInvIdent? g0
      | throwError "{tacName}: on `SepWP` goal, no `ImgCallInv` hypothesis found in context"
    let hSymId ← freshIdent `hsym_wpx
    evalTactic (← `(tactic| try (
      have $hSymId:ident := ($hinvId).2
      try simp only [wp_norm, arm64_norm] at $hSymId:ident)))
    inImageKitCall tacName hcall hinvId arg?
    let gsRaw ← getGoals
    let mut gs : List MVarId := []
    for m0 in gsRaw do
      setGoals [m0]
      evalTactic (← `(tactic| try clear $hSymId:ident))
      gs := gs ++ (← getGoals)
    let mut out : List MVarId := []
    for m in gs do
      let m' ← m.tryClearMany #[oldFv]
      out := out ++ [m']
    setGoals out
  else
    throwError "{tacName}: goal is neither `SepWPpX` nor `SepWP`:{indentExpr gty}"

syntax (name := wpxCall) "wpx_call" ppSpace colGt term:max (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wpx_call $hcall) => wpxCallCore "wpx_call" hcall none
  | `(tactic| wpx_call $hcall $arg) => wpxCallCore "wpx_call" hcall (some arg)

open Lean Elab Tactic Meta in
elab "wpx_cut" ppSpace colGt mid:term : tactic => do
  let g0 ← getMainGoal
  let some (hinvId, oldFv) ← findLatestInvIdent? g0
    | throwError "wpx_cut: no `ImgCallInv` hypothesis in context"
  evalTactic (← `(tactic| apply sepWP_cut_inv $mid $hinvId))
  let g1 ← getMainGoal
  let g2 ← g1.tryClearMany #[oldFv]
  setGoals ([g2] ++ (← getGoals).tail)

open Lean Elab Tactic Meta in
elab "wpx_steps" : tactic => do
  let g0 ← getMainGoal
  let some (hinvId, oldFv) ← findLatestInvIdent? g0
    | evalTactic (← `(tactic| wp_steps))
      return
  let snap ← saveState
  evalTactic (← `(tactic| wp_steps))
  let gs ← getGoals
  let gAfter :: _ := gs | return
  let tyAfter ← gAfter.withContext do instantiateMVars (← gAfter.getType)
  let tyAfter := tyAfter.consumeMData
  if !tyAfter.isAppOfArity ``ProofLib.SepWP 6 then return
  let sCur := tyAfter.getArg! 2
  let hasStore := (sCur.find? fun e =>
    e.isConstOf ``Arm64.State.setMem ||
    e.isConstOf ``Arm64.Memory.writeBytes ||
    e.isConstOf ``Arm64.Memory.write8 ||
    e.isConstOf ``Arm64.Memory.write32 ||
    e.isConstOf ``Arm64.Memory.write64 ||
    e.isConstOf ``Arm64.Memory.write128).isSome
  if !hasStore then return
  let midExpr ← gAfter.withContext do
    let pcRaw ← mkAppM ``Arm64.State.pc #[sCur]
    let midMVar ← mkFreshExprMVar (← inferType pcRaw)
    let eqGoal ← mkFreshExprMVar (← mkEq pcRaw midMVar)
    setGoals [eqGoal.mvarId!]
    let ok ← tryTacticCatchRuntimeBool do
      evalTactic (← `(tactic| try wp_norm_lhs))
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| rfl))
    if ok then
      instantiateMVars midMVar
    else
      whnf (← instantiateMVars pcRaw)
  snap.restore
  let midStx ← g0.withContext (Term.exprToSyntax midExpr)
  let newInv ← freshIdent `hinv_step
  evalTactic (← `(tactic| apply sepWP_cut_inv ($midStx) $hinvId))
  let gCut ← getMainGoal
  let gCutClean ← gCut.tryClearMany #[oldFv]
  setGoals ([gCutClean] ++ (← getGoals).tail)
  evalTactic (← `(tactic| wp_steps))
  evalTactic (← `(tactic| apply ProofLib.SepWP.done (by first | rfl | wp_norm_goal) (by first | rfl | wp_norm_lhs)))
  evalTactic (← `(tactic| intro $newInv:ident))

open Lean Elab Tactic Meta in
elab "wpx_apply" : tactic => do
  let g ← getMainGoal
  let cands ← g.withContext do
    let mut acc : Array Ident := #[]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail || decl.isAuxDecl || decl.userName.hasMacroScopes then
        continue
      let ty ← instantiateMVars decl.type
      if ty.consumeMData.isAppOfArity ``Arm64.subroutine_ok 4 then
        acc := acc.push (mkIdent decl.userName)
    return acc
  for h in cands do
    if ← tryTacticCatchRuntimeBool (wpxCallCore "wpx_apply" h none) then
      return
  throwError "wpx_apply: no matching `subroutine_ok` hypothesis in local context"

open Lean Elab Tactic Meta in
elab "wp_ac_to " rhs:term : tactic => do
  let g ← getMainGoal
  let ty := (← g.withContext do instantiateMVars (← g.getType)).consumeMData
  if ty.isAppOfArity ``SepWPpX 8 then
    evalTactic (← `(tactic| refine SepWPpX.weaken_pre (P' := $rhs) (Entails.of_eq (by ac_rfl)) ?_))
  else
    evalTactic (← `(tactic| refine ProofLib.SepWP.weaken_pre (P' := $rhs) (Entails.of_eq (by ac_rfl)) ?_))

macro "wpx_of_sepWP" ppSpace "(" _id:ident ":=" mid:term ")" : tactic =>
  `(tactic| (apply SepWPpX.of_sepWP_inv (mid := $mid); intro _hinv_blk))

macro "wpx_of_sepWP_ret" : tactic =>
  `(tactic| (apply SepWPpX.of_sepWP_ret_inv; intro _hinv_ret))

macro "entails_ac_to " rhs:term : tactic =>
  `(tactic| refine Entails.trans (Entails.of_eq (by ac_rfl)) (show $rhs ⊢ _ from ?_))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
